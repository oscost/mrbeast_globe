const form = document.getElementById("input-form");
const textarea = document.getElementById("locations");
const summaryEl = document.getElementById("summary");
const errorsEl = document.getElementById("errors");
const tripletTableSummaryEl = document.getElementById("triplet-table-summary");
const resultsEl = document.getElementById("results");
const cutoffRangeEl = document.getElementById("cutoff-range");
const cutoffInputEl = document.getElementById("cutoff-input");
const plotCutoffCirclesEl = document.getElementById("plot-cutoff-circles");
const minLocationsRangeEl = document.getElementById("min-locations-range");
const minLocationsInputEl = document.getElementById("min-locations-input");
const mapSvgEl = document.getElementById("map-svg");
const mapCountEl = document.getElementById("map-count");
const globeSvgEl = document.getElementById("globe-svg");
const globeCountEl = document.getElementById("globe-count");
const globeResetBtnEl = document.getElementById("globe-reset-btn");
const globeLabelsToggleEl = document.getElementById("globe-labels-toggle");
const overlayLegendEl = document.getElementById("overlay-legend");
const tripletRowsEl = document.getElementById("triplet-rows");
const addTripletBtnEl = document.getElementById("add-triplet-btn");
const plotTripletsBtnEl = document.getElementById("plot-triplets-btn");
const fitInfoEl = document.getElementById("fit-info");
const intersectionAEl = document.getElementById("intersection-a");
const intersectionBEl = document.getElementById("intersection-b");
const intersectionCalcEl = document.getElementById("intersection-calc");
const intersectionSelectedEl = document.getElementById("intersection-selected");
const intersectionResultsEl = document.getElementById("intersection-results");
const bestNInputEl = document.getElementById("best-n-input");
const bestNBtnEl = document.getElementById("best-n-btn");
const bestNSummaryEl = document.getElementById("best-n-summary");
const set1WordsEl = document.getElementById("set1-words");
const set2WordsEl = document.getElementById("set2-words");
const pairsPerCircleEl = document.getElementById("pairs-per-circle");
const generateWordCirclesBtnEl = document.getElementById("generate-word-circles-btn");
const wordCircleStatusEl = document.getElementById("word-circle-status");
const wordCircleErrorsEl = document.getElementById("word-circle-errors");
const wordCircleResultsEl = document.getElementById("word-circle-results");

const DEG_TO_RAD = Math.PI / 180;
const RAD_TO_DEG = 180 / Math.PI;
const EARTH_RADIUS_MILES = 3958.7613;

const MAP_WIDTH = 720;
const MAP_HEIGHT = 360;
const GLOBE_SIZE = 360;
const GLOBE_RADIUS = 160;
const SVG_NS = "http://www.w3.org/2000/svg";
const OVERLAY_COLORS = ["#ff5f6d", "#4ade80", "#60a5fa", "#f59e0b", "#f472b6", "#22d3ee"];

const state = {
  points: [],
  pairCandidates: [],
  pairSetRows: [],
  qualifyingPairCount: 0,
  tripletCandidates: [],
  plottedTriplets: [],
  bestNOverlays: [],
  nextRowId: 1,
  cutoffMiles: Number(cutoffRangeEl.value) || 10,
  userTouchedCutoff: false,
  showCutoffCircles: false,
  minLocations: Number(minLocationsRangeEl.value) || 3,
  userTouchedMinLocations: false,
  globeCenter: null,
  globeUserControlled: false
};

function clamp(value, min, max) {
  return Math.max(min, Math.min(max, value));
}

function wrapLongitude(value) {
  const wrapped = ((value + 180) % 360 + 360) % 360 - 180;
  return wrapped;
}

function parseWordLine(rawLine) {
  const trimmed = String(rawLine || "").trim();
  if (!trimmed) {
    return null;
  }

  const possibleLocation = splitLocationLine(trimmed);
  if (possibleLocation) {
    const latParsed = parseCoordinateToken(possibleLocation.latToken, "latitude");
    const lonParsed = parseCoordinateToken(possibleLocation.lonToken, "longitude");
    if (!latParsed.error && !lonParsed.error) {
      const lat = latParsed.value;
      const lon = lonParsed.value;
      if (lat >= -90 && lat <= 90 && lon >= -180 && lon <= 180) {
        const cleanedName = possibleLocation.name
          .replace(/^["']+|["']+$/g, "")
          .replace(/[,;]+$/, "")
          .trim();
        if (!cleanedName) {
          return null;
        }
        const latRad = lat * DEG_TO_RAD;
        const lonRad = lon * DEG_TO_RAD;
        const cosLat = Math.cos(latRad);
        return {
          name: cleanedName,
          lat,
          lon,
          vector: [
            cosLat * Math.cos(lonRad),
            cosLat * Math.sin(lonRad),
            Math.sin(latRad)
          ]
        };
      }
    }
  }

  const cleaned = trimmed
    .replace(/^["']+|["']+$/g, "")
    .replace(/[,;]+$/, "")
    .trim();
  if (!cleaned) {
    return null;
  }
  return { name: cleaned, lat: null, lon: null, vector: null };
}

function parseWordSet(input) {
  if (Array.isArray(input)) {
    return input
      .flatMap((item) => String(item).split(/\r?\n/))
      .flatMap((line) => line.split(";"))
      .map((line) => parseWordLine(line))
      .filter(Boolean);
  }
  if (typeof input !== "string") {
    return [];
  }
  return input
    .split(/\r?\n/)
    .flatMap((line) => line.split(";"))
    .map((line) => parseWordLine(line))
    .filter(Boolean);
}

function findDuplicates(items) {
  const seen = new Set();
  const duplicates = new Set();
  items.forEach((item) => {
    if (seen.has(item)) {
      duplicates.add(item);
      return;
    }
    seen.add(item);
  });
  return [...duplicates];
}

function distributeCounts(total, minPerBucket) {
  if (total <= 0) {
    return [];
  }
  const safeMin = Math.max(1, Math.floor(minPerBucket) || 1);
  if (total <= safeMin) {
    return [total];
  }
  const bucketCount = Math.max(1, Math.floor(total / safeMin));
  const base = Math.floor(total / bucketCount);
  const extra = total % bucketCount;
  const counts = [];
  for (let idx = 0; idx < bucketCount; idx += 1) {
    counts.push(base + (idx < extra ? 1 : 0));
  }
  return counts;
}

function computeBestFitGreatCircleFromVectors(vectors) {
  if (!vectors || vectors.length < 2) {
    return null;
  }

  const matrix = [
    [0, 0, 0],
    [0, 0, 0],
    [0, 0, 0]
  ];
  vectors.forEach((v) => {
    for (let i = 0; i < 3; i += 1) {
      for (let j = 0; j < 3; j += 1) {
        matrix[i][j] += v[i] * v[j];
      }
    }
  });

  const { eigenvalues, eigenvectors } = jacobiEigenSymmetric3(matrix);
  let minIndex = 0;
  if (eigenvalues[1] < eigenvalues[minIndex]) {
    minIndex = 1;
  }
  if (eigenvalues[2] < eigenvalues[minIndex]) {
    minIndex = 2;
  }

  const rawNormal = [
    eigenvectors[0][minIndex],
    eigenvectors[1][minIndex],
    eigenvectors[2][minIndex]
  ];
  const normal = canonicalizeNormal(normalize3(rawNormal));
  if (!normal) {
    return null;
  }

  const distances = vectors.map((v) => distanceToGreatCircleMiles(normal, v));
  const total = distances.reduce((sum, value) => sum + value, 0);
  return {
    normal,
    maxDistanceMiles: Math.max(...distances),
    avgDistanceMiles: total / distances.length
  };
}

function vectorAngularDistanceMiles(a, b) {
  const dot = clamp(dot3(a, b), -1, 1);
  return Math.acos(dot) * EARTH_RADIUS_MILES;
}

function buildOptimizedCircleGroups(set1, set2, groupSizes) {
  const remainingSet1 = set1.slice();
  const remainingSet2 = set2.slice();
  const circles = [];

  groupSizes.forEach((pairCount) => {
    const circleSet1 = [];
    const circleSet2 = [];
    const circleVectors = [];

    for (let pairIndex = 0; pairIndex < pairCount; pairIndex += 1) {
      let best = null;
      for (let i = 0; i < remainingSet1.length; i += 1) {
        const candidate1 = remainingSet1[i];
        for (let j = 0; j < remainingSet2.length; j += 1) {
          const candidate2 = remainingSet2[j];
          const vectors = circleVectors.concat([candidate1.vector, candidate2.vector]);
          const fit = computeBestFitGreatCircleFromVectors(vectors);
          if (!fit) {
            continue;
          }
          const pairDistance = vectorAngularDistanceMiles(candidate1.vector, candidate2.vector);
          if (
            !best ||
            fit.maxDistanceMiles < best.score - 1e-9 ||
            (Math.abs(fit.maxDistanceMiles - best.score) < 1e-9 && pairDistance < best.pairDistance)
          ) {
            best = {
              index1: i,
              index2: j,
              score: fit.maxDistanceMiles,
              pairDistance
            };
          }
        }
      }

      if (!best) {
        break;
      }

      const chosen1 = remainingSet1.splice(best.index1, 1)[0];
      const chosen2 = remainingSet2.splice(best.index2, 1)[0];
      circleSet1.push(chosen1);
      circleSet2.push(chosen2);
      circleVectors.push(chosen1.vector, chosen2.vector);
    }

    const fit = computeBestFitGreatCircleFromVectors(circleVectors);
    circles.push({
      set1: circleSet1,
      set2: circleSet2,
      fit
    });
  });

  return circles;
}

function buildAlternatingGreatCircles(rawSet1, rawSet2, options = {}) {
  const set1 = parseWordSet(rawSet1);
  const set2 = parseWordSet(rawSet2);
  const minPairsPerCircle = Math.max(1, Math.floor(options.pairsPerCircle || 3));

  const duplicates1 = findDuplicates(set1.map((item) => item.name));
  const duplicates2 = findDuplicates(set2.map((item) => item.name));
  if (duplicates1.length || duplicates2.length) {
    throw new Error(
      [
        duplicates1.length
          ? `Set 1 has duplicate word(s): ${duplicates1.join(", ")}.`
          : null,
        duplicates2.length
          ? `Set 2 has duplicate word(s): ${duplicates2.join(", ")}.`
          : null
      ]
        .filter(Boolean)
        .join(" ")
    );
  }

  if (!set2.length) {
    return { circles: [], unmatchedSet1: set1.map((item) => item.name) };
  }
  if (set1.length < set2.length) {
    throw new Error(
      `Need at least ${set2.length} unique Set 1 word(s) to alternate with all Set 2 words.`
    );
  }

  const groupSizes = distributeCounts(set2.length, minPairsPerCircle);
  const canOptimize = set1.every((item) => item.vector) && set2.every((item) => item.vector);
  const shouldOptimize = options.optimize !== false && canOptimize;

  let circles = [];
  let optimizationUsed = false;
  let optimizationNote = "";

  if (shouldOptimize) {
    const optimized = buildOptimizedCircleGroups(set1, set2, groupSizes);
    circles = optimized.map((circle, circleIndex) => {
      const points = [];
      const set1Words = circle.set1.map((item) => item.name);
      const set2Words = circle.set2.map((item) => item.name);
      for (let i = 0; i < set1Words.length; i += 1) {
        points.push(set1Words[i], set2Words[i]);
      }
      return {
        circle: circleIndex + 1,
        points,
        set1Words,
        set2Words,
        maxDistanceMiles: circle.fit ? circle.fit.maxDistanceMiles : null,
        avgDistanceMiles: circle.fit ? circle.fit.avgDistanceMiles : null
      };
    });
    optimizationUsed = true;
  } else {
    const pairs = set2.map((word2, index) => ({
      set1: set1[index],
      set2: word2
    }));
    let pairCursor = 0;
    circles = groupSizes.map((pairCount, circleIndex) => {
      const pairsInCircle = pairs.slice(pairCursor, pairCursor + pairCount);
      pairCursor += pairCount;
      const points = [];
      const set1Words = [];
      const set2Words = [];
      const vectors = [];
      pairsInCircle.forEach((pair) => {
        set1Words.push(pair.set1.name);
        set2Words.push(pair.set2.name);
        points.push(pair.set1.name, pair.set2.name);
        if (pair.set1.vector && pair.set2.vector) {
          vectors.push(pair.set1.vector, pair.set2.vector);
        }
      });
      const fit = vectors.length ? computeBestFitGreatCircleFromVectors(vectors) : null;
      return {
        circle: circleIndex + 1,
        points,
        set1Words,
        set2Words,
        maxDistanceMiles: fit ? fit.maxDistanceMiles : null,
        avgDistanceMiles: fit ? fit.avgDistanceMiles : null
      };
    });
    if (!canOptimize) {
      optimizationNote = "Optimization skipped because some entries lack coordinates.";
    }
  }

  return {
    circles,
    unmatchedSet1: set1.slice(set2.length).map((item) => item.name),
    optimizationUsed,
    optimizationNote
  };
}

function clearWordCircleOutput() {
  if (wordCircleStatusEl) {
    wordCircleStatusEl.textContent = "";
  }
  if (wordCircleErrorsEl) {
    wordCircleErrorsEl.textContent = "";
  }
  if (wordCircleResultsEl) {
    wordCircleResultsEl.replaceChildren();
  }
}

function renderWordCircleOutput(result) {
  if (!wordCircleStatusEl || !wordCircleResultsEl || !wordCircleErrorsEl) {
    return;
  }
  wordCircleErrorsEl.textContent = "";
  wordCircleResultsEl.replaceChildren();

  const totalPoints = result.circles.reduce((sum, circle) => sum + circle.points.length, 0);
  wordCircleStatusEl.textContent =
    `Created ${result.circles.length} circle${result.circles.length === 1 ? "" : "s"} ` +
    `with ${totalPoints} alternating points.` +
    (result.optimizationUsed ? " Optimized for best-fit great circles." : "");
  if (result.optimizationNote) {
    wordCircleStatusEl.textContent = `${wordCircleStatusEl.textContent} ${result.optimizationNote}`;
  }

  result.circles.forEach((circle) => {
    const block = document.createElement("article");
    block.className = "word-circle-result-block";

    const title = document.createElement("h3");
    title.className = "word-circle-result-title";
    const distanceInfo =
      circle.maxDistanceMiles != null
        ? ` | max ${circle.maxDistanceMiles.toFixed(2)} mi, avg ${circle.avgDistanceMiles.toFixed(2)} mi`
        : "";
    title.textContent =
      `Circle ${circle.circle}: ${circle.set2Words.length} Set 2 word` +
      `${circle.set2Words.length === 1 ? "" : "s"}${distanceInfo}`;

    const points = document.createElement("p");
    points.className = "word-circle-result-points";
    points.textContent = circle.points.join(" -> ");

    block.appendChild(title);
    block.appendChild(points);
    wordCircleResultsEl.appendChild(block);
  });

  if (result.unmatchedSet1.length) {
    const unused = document.createElement("p");
    unused.className = "summary";
    unused.textContent = `Unused Set 1 words: ${result.unmatchedSet1.join(", ")}`;
    wordCircleResultsEl.appendChild(unused);
  }
}

function generateWordCirclesFromInputs() {
  if (!set1WordsEl || !set2WordsEl || !pairsPerCircleEl) {
    return;
  }

  clearWordCircleOutput();

  const requestedPairs = Number(pairsPerCircleEl.value);
  const safePairs = Number.isFinite(requestedPairs) ? requestedPairs : 3;

  try {
    const result = buildAlternatingGreatCircles(set1WordsEl.value, set2WordsEl.value, {
      pairsPerCircle: safePairs
    });
    renderWordCircleOutput(result);
  } catch (error) {
    if (!wordCircleErrorsEl) {
      return;
    }
    const message = error instanceof Error ? error.message : String(error);
    wordCircleErrorsEl.textContent = message;
  }
}

function dot3(a, b) {
  return a[0] * b[0] + a[1] * b[1] + a[2] * b[2];
}

function cross3(a, b) {
  return [
    a[1] * b[2] - a[2] * b[1],
    a[2] * b[0] - a[0] * b[2],
    a[0] * b[1] - a[1] * b[0]
  ];
}

function normalize3(v) {
  const mag = Math.hypot(v[0], v[1], v[2]);
  if (mag < 1e-15) {
    return null;
  }
  return [v[0] / mag, v[1] / mag, v[2] / mag];
}

function canonicalizeNormal(normal) {
  if (!normal) {
    return null;
  }
  const eps = 1e-12;
  if (normal[0] < -eps) {
    return [-normal[0], -normal[1], -normal[2]];
  }
  if (Math.abs(normal[0]) <= eps && normal[1] < -eps) {
    return [-normal[0], -normal[1], -normal[2]];
  }
  if (Math.abs(normal[0]) <= eps && Math.abs(normal[1]) <= eps && normal[2] < -eps) {
    return [-normal[0], -normal[1], -normal[2]];
  }
  return normal;
}

function distanceToGreatCircleMiles(normal, pointVector) {
  const signed = Math.abs(dot3(normal, pointVector));
  const angle = Math.asin(clamp(signed, 0, 1));
  return angle * EARTH_RADIUS_MILES;
}

function totalDistanceToGreatCircleMiles(normal) {
  return state.points.reduce(
    (sum, point) => sum + distanceToGreatCircleMiles(normal, point.vector),
    0
  );
}

function computeClosestUnaddedPoint(normal, indices) {
  const selected = new Set(indices);
  let best = null;

  state.points.forEach((point) => {
    if (selected.has(point.index)) {
      return;
    }
    const distance = distanceToGreatCircleMiles(normal, point.vector);
    if (!best || distance < best.distance) {
      best = { point, distance };
    }
  });

  return best;
}

function parseCoordinateToken(rawToken, axis) {
  const token = rawToken.trim().replaceAll("º", "°");
  const match = token.match(
    /^([NSEW])?\s*([+-]?\d+(?:\.\d+)?)\s*(?:°|deg(?:rees)?)?\s*([NSEW])?$/i
  );

  if (!match) {
    return { error: `invalid ${axis} format` };
  }

  const hemiPrefix = match[1] ? match[1].toUpperCase() : null;
  const hemiSuffix = match[3] ? match[3].toUpperCase() : null;
  if (hemiPrefix && hemiSuffix && hemiPrefix !== hemiSuffix) {
    return { error: `conflicting hemisphere markers in ${axis}` };
  }
  const hemisphere = hemiSuffix || hemiPrefix;

  const value = Number(match[2]);
  if (!Number.isFinite(value)) {
    return { error: `${axis} is not numeric` };
  }

  const allowed = axis === "latitude" ? ["N", "S"] : ["E", "W"];
  if (hemisphere && !allowed.includes(hemisphere)) {
    return {
      error:
        axis === "latitude"
          ? "latitude hemisphere must be N or S"
          : "longitude hemisphere must be E or W"
    };
  }

  let signedValue = value;
  if (hemisphere) {
    const sign = hemisphere === "N" || hemisphere === "E" ? 1 : -1;
    signedValue = Math.abs(value) * sign;
  }

  return { value: signedValue };
}

function splitLocationLine(trimmed) {
  const commaParts = trimmed.split(",");

  if (commaParts.length >= 3) {
    return {
      name: commaParts.slice(0, -2).join(",").trim(),
      latToken: commaParts[commaParts.length - 2].trim(),
      lonToken: commaParts[commaParts.length - 1].trim()
    };
  }

  if (commaParts.length === 2) {
    const lonToken = commaParts[1].trim();
    const left = commaParts[0].trim();
    const leftMatch = left.match(
      /^(.*?)[\t ]+((?:[NSEW]\s*)?[+-]?\d+(?:\.\d+)?\s*(?:°|º|deg(?:rees)?)?\s*(?:[NSEW])?)$/i
    );

    if (leftMatch) {
      const name = leftMatch[1].trim().replace(/[,;]+$/, "").trim();
      const latToken = leftMatch[2].trim();
      return { name, latToken, lonToken };
    }
  }

  return null;
}

function parseLocations(rawText) {
  const lines = rawText.split(/\r?\n/);
  const points = [];
  const errors = [];

  lines.forEach((line, index) => {
    const trimmed = line.trim();
    if (!trimmed) {
      return;
    }

    const split = splitLocationLine(trimmed);
    if (!split) {
      errors.push(
        `Line ${index + 1}: expected "<name>, LAT, LONG" (LAT/LONG can use N/S/E/W).`
      );
      return;
    }

    const name = split.name;
    const latStr = split.latToken;
    const lonStr = split.lonToken;

    if (!name) {
      errors.push(`Line ${index + 1}: missing place name.`);
      return;
    }

    const latParsed = parseCoordinateToken(latStr, "latitude");
    const lonParsed = parseCoordinateToken(lonStr, "longitude");
    if (latParsed.error || lonParsed.error) {
      const details = [latParsed.error, lonParsed.error].filter(Boolean).join("; ");
      errors.push(`Line ${index + 1}: ${details}.`);
      return;
    }
    const lat = latParsed.value;
    const lon = lonParsed.value;

    if (lat < -90 || lat > 90) {
      errors.push(`Line ${index + 1}: latitude must be in [-90, 90].`);
      return;
    }

    if (lon < -180 || lon > 180) {
      errors.push(`Line ${index + 1}: longitude must be in [-180, 180].`);
      return;
    }

    const latRad = lat * DEG_TO_RAD;
    const lonRad = lon * DEG_TO_RAD;
    const cosLat = Math.cos(latRad);

    points.push({
      index: points.length,
      name,
      lat,
      lon,
      vector: [
        cosLat * Math.cos(lonRad),
        cosLat * Math.sin(lonRad),
        Math.sin(latRad)
      ]
    });
  });

  return { points, errors };
}

function jacobiEigenSymmetric3(matrix) {
  const a = [
    [...matrix[0]],
    [...matrix[1]],
    [...matrix[2]]
  ];
  const v = [
    [1, 0, 0],
    [0, 1, 0],
    [0, 0, 1]
  ];

  const offDiagNorm = () => {
    const a01 = a[0][1];
    const a02 = a[0][2];
    const a12 = a[1][2];
    return Math.sqrt(a01 * a01 + a02 * a02 + a12 * a12);
  };

  for (let iter = 0; iter < 24; iter += 1) {
    if (offDiagNorm() < 1e-12) {
      break;
    }

    let p = 0;
    let q = 1;
    let max = Math.abs(a[0][1]);
    const candidates = [
      [0, 2, Math.abs(a[0][2])],
      [1, 2, Math.abs(a[1][2])]
    ];
    candidates.forEach(([i, j, value]) => {
      if (value > max) {
        p = i;
        q = j;
        max = value;
      }
    });

    if (max < 1e-14) {
      break;
    }

    const app = a[p][p];
    const aqq = a[q][q];
    const apq = a[p][q];
    const tau = (aqq - app) / (2 * apq);
    const t = Math.sign(tau) / (Math.abs(tau) + Math.sqrt(1 + tau * tau));
    const c = 1 / Math.sqrt(1 + t * t);
    const s = t * c;

    a[p][p] = app - t * apq;
    a[q][q] = aqq + t * apq;
    a[p][q] = 0;
    a[q][p] = 0;

    for (let r = 0; r < 3; r += 1) {
      if (r !== p && r !== q) {
        const arp = a[r][p];
        const arq = a[r][q];
        const newArp = c * arp - s * arq;
        const newArq = s * arp + c * arq;
        a[r][p] = newArp;
        a[p][r] = newArp;
        a[r][q] = newArq;
        a[q][r] = newArq;
      }
    }

    for (let r = 0; r < 3; r += 1) {
      const vrp = v[r][p];
      const vrq = v[r][q];
      v[r][p] = c * vrp - s * vrq;
      v[r][q] = s * vrp + c * vrq;
    }
  }

  return {
    eigenvalues: [a[0][0], a[1][1], a[2][2]],
    eigenvectors: v
  };
}

function computeBestFitGreatCircle(indices) {
  const vectors = indices.map((idx) => state.points[idx].vector);
  const matrix = [
    [0, 0, 0],
    [0, 0, 0],
    [0, 0, 0]
  ];

  vectors.forEach((v) => {
    for (let i = 0; i < 3; i += 1) {
      for (let j = 0; j < 3; j += 1) {
        matrix[i][j] += v[i] * v[j];
      }
    }
  });

  const { eigenvalues, eigenvectors } = jacobiEigenSymmetric3(matrix);
  let minIndex = 0;
  if (eigenvalues[1] < eigenvalues[minIndex]) {
    minIndex = 1;
  }
  if (eigenvalues[2] < eigenvalues[minIndex]) {
    minIndex = 2;
  }

  const rawNormal = [
    eigenvectors[0][minIndex],
    eigenvectors[1][minIndex],
    eigenvectors[2][minIndex]
  ];
  const normal = canonicalizeNormal(normalize3(rawNormal));
  if (!normal) {
    return null;
  }

  const selectedDistances = indices.map((idx) =>
    distanceToGreatCircleMiles(normal, state.points[idx].vector)
  );
  return {
    normal,
    indices,
    names: indices.map((idx) => state.points[idx].name),
    maxDistanceMiles: Math.max(...selectedDistances)
  };
}

function buildPairCandidates() {
  const pairs = [];
  for (let i = 0; i < state.points.length - 1; i += 1) {
    for (let j = i + 1; j < state.points.length; j += 1) {
      const normal = canonicalizeNormal(normalize3(cross3(state.points[i].vector, state.points[j].vector)));
      if (!normal) {
        continue;
      }

      const distances = state.points.map((point) => distanceToGreatCircleMiles(normal, point.vector));
      const maxDistanceMiles = Math.max(...distances);
      pairs.push({
        pairIndices: [i, j],
        pairNames: [state.points[i].name, state.points[j].name],
        normal,
        distances,
        maxDistanceMiles
      });
    }
  }
  return pairs;
}

function setMinLocationsValue(value) {
  const min = Number(minLocationsRangeEl.min) || 3;
  const max = Number(minLocationsRangeEl.max) || Math.max(3, state.points.length);
  const clamped = Math.round(clamp(value, min, max));
  state.minLocations = clamped;
  minLocationsRangeEl.value = String(clamped);
  minLocationsInputEl.value = String(clamped);
}

function configureMinLocationsControls() {
  const enabled = state.points.length >= 3;
  minLocationsRangeEl.disabled = !enabled;
  minLocationsInputEl.disabled = !enabled;
  const maxValue = Math.max(3, state.points.length);
  minLocationsRangeEl.min = "3";
  minLocationsRangeEl.max = String(maxValue);
  minLocationsInputEl.min = "3";
  minLocationsInputEl.max = String(maxValue);

  if (!enabled) {
    setMinLocationsValue(3);
    return;
  }

  if (!state.userTouchedMinLocations) {
    setMinLocationsValue(3);
  } else {
    setMinLocationsValue(state.minLocations);
  }
}

function computeMaxDistanceForIndices(normal, indices) {
  if (!indices.length) {
    return 0;
  }
  return Math.max(
    ...indices.map((idx) => distanceToGreatCircleMiles(normal, state.points[idx].vector))
  );
}

function buildPairLocationSetRows() {
  const rowsByKey = new Map();
  let qualifyingPairCount = 0;

  state.pairCandidates.forEach((pair) => {
    const locationIndices = [];
    for (let idx = 0; idx < pair.distances.length; idx += 1) {
      if (pair.distances[idx] <= state.cutoffMiles + 1e-9) {
        locationIndices.push(idx);
      }
    }

    if (locationIndices.length < state.minLocations) {
      return;
    }

    qualifyingPairCount += 1;
    const key = locationIndices.join(",");
    const existing = rowsByKey.get(key);
    if (existing) {
      existing.supportPairCount += 1;
      if (pair.pairNames.join(" | ").localeCompare(existing.examplePair) < 0) {
        existing.examplePair = pair.pairNames.join(" | ");
      }
      return;
    }

    const bestFit = locationIndices.length >= 3 ? computeBestFitGreatCircle(locationIndices) : null;
    const bestFitNormal = bestFit ? bestFit.normal : pair.normal;
    rowsByKey.set(key, {
      locationIndices,
      locationNames: locationIndices.map((idx) => state.points[idx].name),
      supportPairCount: 1,
      examplePair: pair.pairNames.join(" | "),
      bestFitNormal,
      maxDistanceMiles: computeMaxDistanceForIndices(bestFitNormal, locationIndices)
    });
  });

  const rows = [...rowsByKey.values()];
  rows.sort((a, b) => {
    if (b.locationIndices.length !== a.locationIndices.length) {
      return b.locationIndices.length - a.locationIndices.length;
    }
    if (b.supportPairCount !== a.supportPairCount) {
      return b.supportPairCount - a.supportPairCount;
    }
    if (a.maxDistanceMiles !== b.maxDistanceMiles) {
      return a.maxDistanceMiles - b.maxDistanceMiles;
    }
    return a.locationNames.join("|").localeCompare(b.locationNames.join("|"));
  });

  return { rows, qualifyingPairCount };
}

function setCutoffValue(cutoffMiles) {
  const min = Number(cutoffRangeEl.min) || 0;
  const max = Number(cutoffRangeEl.max) || 0;
  const integerCutoff = Math.round(clamp(cutoffMiles, min, max));

  state.cutoffMiles = integerCutoff;
  cutoffRangeEl.value = String(integerCutoff);
  cutoffInputEl.value = String(integerCutoff);
}

function configureCutoffControls() {
  if (!state.pairCandidates.length) {
    cutoffRangeEl.min = "0";
    cutoffRangeEl.max = "0";
    cutoffRangeEl.disabled = true;
    cutoffInputEl.min = "0";
    cutoffInputEl.max = "0";
    cutoffInputEl.disabled = true;
    setCutoffValue(0);
    return;
  }

  const maxDistance = Math.max(...state.pairCandidates.map((pair) => pair.maxDistanceMiles));
  const sliderMax = Math.max(1, Math.ceil(maxDistance));

  cutoffRangeEl.min = "0";
  cutoffRangeEl.max = String(sliderMax);
  cutoffRangeEl.disabled = false;
  cutoffInputEl.min = "0";
  cutoffInputEl.max = String(sliderMax);
  cutoffInputEl.disabled = false;

  if (!state.userTouchedCutoff) {
    setCutoffValue(Math.min(10, sliderMax));
  } else if (state.cutoffMiles > sliderMax) {
    setCutoffValue(sliderMax);
  } else {
    setCutoffValue(state.cutoffMiles);
  }
}

function buildTripletCandidates() {
  const candidates = [];
  for (let i = 0; i < state.points.length - 2; i += 1) {
    for (let j = i + 1; j < state.points.length - 1; j += 1) {
      for (let k = j + 1; k < state.points.length; k += 1) {
        const fit = computeBestFitGreatCircle([i, j, k]);
        if (!fit) {
          continue;
        }
        candidates.push({
          indices: [i, j, k],
          names: [state.points[i].name, state.points[j].name, state.points[k].name],
          normal: fit.normal,
          maxDistanceMiles: fit.maxDistanceMiles
        });
      }
    }
  }

  candidates.sort((a, b) => {
    if (a.maxDistanceMiles !== b.maxDistanceMiles) {
      return a.maxDistanceMiles - b.maxDistanceMiles;
    }
    return a.names.join("|").localeCompare(b.names.join("|"));
  });
  return candidates;
}

function renderTripletTable(rows) {
  resultsEl.replaceChildren();
  if (!rows.length) {
    const empty = document.createElement("p");
    empty.textContent =
      `No deduplicated location sets found with at least ${state.minLocations} locations under cutoff.`;
    resultsEl.appendChild(empty);
    return;
  }

  const scrollWrap = document.createElement("div");
  scrollWrap.className = "results-scroll";

  const table = document.createElement("table");
  const thead = document.createElement("thead");
  const trHead = document.createElement("tr");
  [
    "#",
    "Locations",
    "Location Count",
    "Supporting Pairs",
    "Example Pair",
    "Max Distance To Best-Fit Circle (miles)"
  ].forEach((label) => {
    const th = document.createElement("th");
    th.textContent = label;
    trHead.appendChild(th);
  });
  thead.appendChild(trHead);
  table.appendChild(thead);

  const tbody = document.createElement("tbody");
  rows.forEach((row, index) => {
    const tr = document.createElement("tr");

    const rankCell = document.createElement("td");
    rankCell.className = "mono";
    rankCell.textContent = String(index + 1);
    tr.appendChild(rankCell);

    const locationCell = document.createElement("td");
    locationCell.textContent = row.locationNames.join(" | ");
    tr.appendChild(locationCell);

    const locationCountCell = document.createElement("td");
    locationCountCell.className = "mono";
    locationCountCell.textContent = String(row.locationIndices.length);
    tr.appendChild(locationCountCell);

    const supportCell = document.createElement("td");
    supportCell.className = "mono";
    supportCell.textContent = String(row.supportPairCount);
    tr.appendChild(supportCell);

    const pairCell = document.createElement("td");
    pairCell.textContent = row.examplePair;
    tr.appendChild(pairCell);

    const maxDistanceCell = document.createElement("td");
    maxDistanceCell.className = "mono";
    maxDistanceCell.textContent = row.maxDistanceMiles.toFixed(3);
    tr.appendChild(maxDistanceCell);

    tbody.appendChild(tr);
  });
  table.appendChild(tbody);

  scrollWrap.appendChild(table);
  resultsEl.appendChild(scrollWrap);
}

function getFilteredTripletCandidates() {
  return state.tripletCandidates.filter((row) => row.maxDistanceMiles <= state.cutoffMiles + 1e-9);
}

function getCutoffCircleOverlays() {
  if (!state.showCutoffCircles) {
    return [];
  }

  const filtered = getFilteredTripletCandidates();
  return filtered.map((row, idx) => ({
    ...row,
    color: OVERLAY_COLORS[idx % OVERLAY_COLORS.length]
  }));
}

function getBestNOverlays() {
  return state.bestNOverlays;
}

function getPairSetOverlays() {
  return state.pairSetRows.map((row, idx) => ({
    normal: row.bestFitNormal,
    indices: row.locationIndices,
    names: row.locationNames,
    maxDistanceMiles: row.maxDistanceMiles,
    color: OVERLAY_COLORS[(idx + 2) % OVERLAY_COLORS.length]
  }));
}

function collectOverlayState() {
  const pairSetOverlays = getPairSetOverlays();
  const cutoffOverlays = getCutoffCircleOverlays();
  const manualOverlays = state.plottedTriplets.filter((overlay) => overlay.visible);
  const manualTotal = state.plottedTriplets.length;
  const bestNOverlays = getBestNOverlays();
  const hiddenManualPoints = new Set();
  state.plottedTriplets
    .filter((overlay) => !overlay.visible)
    .forEach((overlay) => {
      overlay.indices.forEach((idx) => hiddenManualPoints.add(idx));
    });
  const overlays = [
    ...pairSetOverlays,
    ...cutoffOverlays,
    ...bestNOverlays,
    ...manualOverlays
  ];
  return {
    pairSetOverlays,
    cutoffOverlays,
    manualOverlays,
    manualTotal,
    bestNOverlays,
    overlays,
    hiddenManualPoints
  };
}

function refreshMapAndLegend() {
  const {
    pairSetOverlays,
    cutoffOverlays,
    manualOverlays,
    manualTotal,
    bestNOverlays,
    overlays,
    hiddenManualPoints
  } = collectOverlayState();

  renderMap(state.points, overlays, hiddenManualPoints);
  renderGlobe(state.points, overlays, hiddenManualPoints);

  overlayLegendEl.replaceChildren();
  if (!overlays.length) {
    const empty = document.createElement("span");
    empty.textContent = "No great circle overlays shown.";
    overlayLegendEl.appendChild(empty);
    return;
  }

  if (pairSetOverlays.length) {
    const line = document.createElement("span");
    line.textContent =
      `Deduplicated-set overlays: ${pairSetOverlays.length} circle` +
      `${pairSetOverlays.length === 1 ? "" : "s"}.`;
    overlayLegendEl.appendChild(line);
  }

  if (state.showCutoffCircles) {
    const line = document.createElement("span");
    line.textContent =
      `Triplet cutoff overlays: ${cutoffOverlays.length} circle` +
      `${cutoffOverlays.length === 1 ? "" : "s"}.`;
    overlayLegendEl.appendChild(line);
  }

  if (bestNOverlays.length) {
    const line = document.createElement("span");
    line.textContent =
      `Top-N best-fit overlays: ${bestNOverlays.length} circle` +
      `${bestNOverlays.length === 1 ? "" : "s"}.`;
    overlayLegendEl.appendChild(line);
  }

  if (manualTotal) {
    const line = document.createElement("span");
    line.textContent =
      `Manual selections: ${manualOverlays.length} visible of ${manualTotal} circle` +
      `${manualTotal === 1 ? "" : "s"}.`;
    overlayLegendEl.appendChild(line);
  }
}

function applyTripletCutoffAndRenderTable() {
  const { rows, qualifyingPairCount } = buildPairLocationSetRows();
  state.pairSetRows = rows;
  state.qualifyingPairCount = qualifyingPairCount;

  tripletTableSummaryEl.textContent =
    `Pair great circles checked: ${state.pairCandidates.length}. ` +
    `Qualifying pairs (>= ${state.minLocations} locations within ${state.cutoffMiles} miles): ${state.qualifyingPairCount}. ` +
    `Deduplicated location sets shown: ${state.pairSetRows.length}.`;

  renderTripletTable(state.pairSetRows);
  refreshMapAndLegend();
}

function refreshGlobeOnly() {
  if (!globeSvgEl) {
    return;
  }
  const { overlays, hiddenManualPoints } = collectOverlayState();
  renderGlobe(state.points, overlays, hiddenManualPoints);
}

function vectorToLatLon(v) {
  const lat = Math.asin(clamp(v[2], -1, 1)) * RAD_TO_DEG;
  const lon = Math.atan2(v[1], v[0]) * RAD_TO_DEG;
  return { lat, lon };
}

function formatCoord(value) {
  return value.toFixed(6);
}

function makeGreatCircleBasis(normal) {
  let ref = Math.abs(normal[2]) < 0.9 ? [0, 0, 1] : [0, 1, 0];
  let u = normalize3(cross3(normal, ref));
  if (!u) {
    ref = [1, 0, 0];
    u = normalize3(cross3(normal, ref));
  }
  if (!u) {
    return null;
  }
  const v = normalize3(cross3(normal, u));
  if (!v) {
    return null;
  }
  return { u, v };
}

function svgEl(tag, attrs) {
  const el = document.createElementNS(SVG_NS, tag);
  Object.entries(attrs).forEach(([key, value]) => {
    el.setAttribute(key, String(value));
  });
  return el;
}

function projectLonToX(lon) {
  return ((lon + 180) / 360) * MAP_WIDTH;
}

function projectLatToY(lat) {
  return ((90 - lat) / 180) * MAP_HEIGHT;
}

function computeGlobeCenter(points) {
  if (!points.length) {
    return { lat: 20, lon: 0 };
  }
  const sum = points.reduce(
    (acc, point) => [acc[0] + point.vector[0], acc[1] + point.vector[1], acc[2] + point.vector[2]],
    [0, 0, 0]
  );
  const normalized = normalize3(sum);
  if (!normalized) {
    return { lat: 20, lon: 0 };
  }
  return vectorToLatLon(normalized);
}

function getGlobeCenter(points) {
  if (state.globeUserControlled && state.globeCenter) {
    return state.globeCenter;
  }
  const computed = computeGlobeCenter(points);
  state.globeCenter = computed;
  return computed;
}

function setGlobeCenter(lat, lon, userControlled) {
  state.globeCenter = { lat, lon };
  state.globeUserControlled = userControlled;
}

function projectToGlobe(lat, lon, centerLat, centerLon, radius) {
  const latRad = lat * DEG_TO_RAD;
  const lonRad = lon * DEG_TO_RAD;
  const centerLatRad = centerLat * DEG_TO_RAD;
  const centerLonRad = centerLon * DEG_TO_RAD;
  const dLon = lonRad - centerLonRad;
  const cosLat = Math.cos(latRad);
  const sinLat = Math.sin(latRad);
  const cosLat0 = Math.cos(centerLatRad);
  const sinLat0 = Math.sin(centerLatRad);
  const cosDLon = Math.cos(dLon);
  const sinDLon = Math.sin(dLon);

  const x = radius * cosLat * sinDLon;
  const y = radius * (cosLat0 * sinLat - sinLat0 * cosLat * cosDLon);
  const z = sinLat0 * sinLat + cosLat0 * cosLat * cosDLon;
  return { x, y, visible: z >= 0 };
}

function pathDataFromSegment(segment) {
  if (segment.length < 2) {
    return "";
  }
  let d = `M ${segment[0][0].toFixed(2)} ${segment[0][1].toFixed(2)}`;
  for (let i = 1; i < segment.length; i += 1) {
    d += ` L ${segment[i][0].toFixed(2)} ${segment[i][1].toFixed(2)}`;
  }
  return d;
}

function drawGreatCircleOverlay(normal, color) {
  const basis = makeGreatCircleBasis(normal);
  if (!basis) {
    return;
  }

  const { u, v } = basis;
  const steps = 540;
  const segments = [];
  let currentSegment = [];
  let prevX = null;

  for (let step = 0; step <= steps; step += 1) {
    const t = (2 * Math.PI * step) / steps;
    const ct = Math.cos(t);
    const st = Math.sin(t);
    const x3 = u[0] * ct + v[0] * st;
    const y3 = u[1] * ct + v[1] * st;
    const z3 = u[2] * ct + v[2] * st;

    const lon = Math.atan2(y3, x3) * RAD_TO_DEG;
    const lat = Math.asin(clamp(z3, -1, 1)) * RAD_TO_DEG;
    const x = projectLonToX(lon);
    const y = projectLatToY(lat);

    if (prevX !== null && Math.abs(x - prevX) > MAP_WIDTH / 2) {
      if (currentSegment.length > 1) {
        segments.push(currentSegment);
      }
      currentSegment = [];
    }

    currentSegment.push([x, y]);
    prevX = x;
  }

  if (currentSegment.length > 1) {
    segments.push(currentSegment);
  }

  segments.forEach((segment) => {
    const d = pathDataFromSegment(segment);
    if (!d) {
      return;
    }
    mapSvgEl.appendChild(
      svgEl("path", {
        d,
        fill: "none",
        stroke: color,
        "stroke-width": 2.2,
        opacity: 0.95,
        "stroke-linejoin": "round",
        "stroke-linecap": "round"
      })
    );
  });
}

function drawGreatCircleOnGlobe(normal, color, centerLat, centerLon, radius, centerX, centerY) {
  if (!globeSvgEl) {
    return;
  }
  const basis = makeGreatCircleBasis(normal);
  if (!basis) {
    return;
  }

  const { u, v } = basis;
  const steps = 540;
  const segments = [];
  let currentSegment = [];

  for (let step = 0; step <= steps; step += 1) {
    const t = (2 * Math.PI * step) / steps;
    const ct = Math.cos(t);
    const st = Math.sin(t);
    const x3 = u[0] * ct + v[0] * st;
    const y3 = u[1] * ct + v[1] * st;
    const z3 = u[2] * ct + v[2] * st;

    const lon = Math.atan2(y3, x3) * RAD_TO_DEG;
    const lat = Math.asin(clamp(z3, -1, 1)) * RAD_TO_DEG;
    const projected = projectToGlobe(lat, lon, centerLat, centerLon, radius);

    if (!projected.visible) {
      if (currentSegment.length > 1) {
        segments.push(currentSegment);
      }
      currentSegment = [];
      continue;
    }

    currentSegment.push([centerX + projected.x, centerY + projected.y]);
  }

  if (currentSegment.length > 1) {
    segments.push(currentSegment);
  }

  segments.forEach((segment) => {
    const d = pathDataFromSegment(segment);
    if (!d) {
      return;
    }
    globeSvgEl.appendChild(
      svgEl("path", {
        d,
        fill: "none",
        stroke: color,
        "stroke-width": 2.2,
        opacity: 0.95,
        "stroke-linejoin": "round",
        "stroke-linecap": "round"
      })
    );
  });
}

function renderMap(points, overlays, hiddenPointIndices = new Set()) {
  mapSvgEl.replaceChildren();
  mapCountEl.textContent = `${points.length} point${points.length === 1 ? "" : "s"} loaded`;

  mapSvgEl.appendChild(
    svgEl("rect", {
      x: 0,
      y: 0,
      width: MAP_WIDTH,
      height: MAP_HEIGHT,
      fill: "#1b2c49"
    })
  );

  for (let lon = -180; lon <= 180; lon += 30) {
    const x = projectLonToX(lon);
    mapSvgEl.appendChild(
      svgEl("line", {
        x1: x,
        y1: 0,
        x2: x,
        y2: MAP_HEIGHT,
        stroke: lon === 0 ? "#314f79" : "#284165",
        "stroke-width": lon === 0 ? 1.7 : 1
      })
    );
  }

  for (let lat = -90; lat <= 90; lat += 30) {
    const y = projectLatToY(lat);
    mapSvgEl.appendChild(
      svgEl("line", {
        x1: 0,
        y1: y,
        x2: MAP_WIDTH,
        y2: y,
        stroke: lat === 0 ? "#314f79" : "#284165",
        "stroke-width": lat === 0 ? 1.7 : 1
      })
    );
  }

  const pointHighlightColors = new Map();
  overlays.forEach((overlay) => {
    drawGreatCircleOverlay(overlay.normal, overlay.color);
    overlay.indices.forEach((pointIndex) => {
      pointHighlightColors.set(pointIndex, overlay.color);
    });
  });

  points.forEach((point) => {
    const x = projectLonToX(point.lon);
    const y = projectLatToY(point.lat);
    const highlightColor = pointHighlightColors.get(point.index);
    if (!highlightColor && hiddenPointIndices.has(point.index)) {
      return;
    }

    mapSvgEl.appendChild(
      svgEl("circle", {
        cx: x,
        cy: y,
        r: highlightColor ? 5.2 : 4,
        fill: highlightColor || "#ffd24d",
        stroke: highlightColor ? "#ffffff" : "#a66a00",
        "stroke-width": highlightColor ? 1.1 : 0.8
      })
    );

    const label = svgEl("text", {
      x: x + 7,
      y: y - 7,
      fill: "#eef4ff",
      "font-size": 12,
      "font-weight": 600
    });
    label.textContent = point.name;
    mapSvgEl.appendChild(label);
  });
}

function renderGlobe(points, overlays, hiddenPointIndices = new Set()) {
  if (!globeSvgEl || !globeCountEl) {
    return;
  }
  globeSvgEl.replaceChildren();
  globeCountEl.textContent = `${points.length} point${points.length === 1 ? "" : "s"} loaded`;

  const center = getGlobeCenter(points);
  const radius = GLOBE_RADIUS;
  const cx = GLOBE_SIZE / 2;
  const cy = GLOBE_SIZE / 2;

  globeSvgEl.appendChild(
    svgEl("circle", {
      cx,
      cy,
      r: radius,
      fill: "#10213d",
      stroke: "#2b466b",
      "stroke-width": 2
    })
  );

  const graticuleColor = "#243c65";
  drawGreatCircleOnGlobe([0, 0, 1], graticuleColor, center.lat, center.lon, radius, cx, cy);
  drawGreatCircleOnGlobe([0, 1, 0], graticuleColor, center.lat, center.lon, radius, cx, cy);

  const pointHighlightColors = new Map();
  overlays.forEach((overlay) => {
    drawGreatCircleOnGlobe(overlay.normal, overlay.color, center.lat, center.lon, radius, cx, cy);
    overlay.indices.forEach((pointIndex) => {
      pointHighlightColors.set(pointIndex, overlay.color);
    });
  });

  points.forEach((point) => {
    const highlightColor = pointHighlightColors.get(point.index);
    if (!highlightColor && hiddenPointIndices.has(point.index)) {
      return;
    }

    const projected = projectToGlobe(point.lat, point.lon, center.lat, center.lon, radius);
    if (!projected.visible) {
      return;
    }

    const labelX = cx + projected.x;
    const labelY = cy + projected.y;

    globeSvgEl.appendChild(
      svgEl("circle", {
        cx: labelX,
        cy: labelY,
        r: highlightColor ? 4.4 : 3.2,
        fill: highlightColor || "#ffd24d",
        stroke: highlightColor ? "#ffffff" : "#a66a00",
        "stroke-width": highlightColor ? 1 : 0.7
      })
    );

    if (!globeLabelsToggleEl || globeLabelsToggleEl.checked) {
      const label = svgEl("text", {
        x: labelX + 6,
        y: labelY - 6,
        fill: "#eef4ff",
        "font-size": 11,
        "font-weight": 600
      });
      label.textContent = point.name;
      globeSvgEl.appendChild(label);
    }
  });
}

function renderOverlayLegend(overlays) {
  overlayLegendEl.replaceChildren();
  if (!overlays.length) {
    const empty = document.createElement("span");
    empty.textContent = "No triplet circles plotted yet.";
    overlayLegendEl.appendChild(empty);
    return;
  }

  overlays.forEach((overlay, index) => {
    const item = document.createElement("div");
    item.className = "overlay-item";

    const swatch = document.createElement("span");
    swatch.className = "overlay-swatch";
    swatch.style.backgroundColor = overlay.color;
    item.appendChild(swatch);

    const text = document.createElement("span");
    text.textContent =
      `Triplet ${index + 1}: ${overlay.names.join(" | ")} ` +
      `(max fit error ${overlay.maxDistanceMiles.toFixed(2)} mi)`;
    item.appendChild(text);

    overlayLegendEl.appendChild(item);
  });
}

function renderErrors(errors) {
  errorsEl.replaceChildren();
  if (!errors.length) {
    return;
  }

  const list = document.createElement("ul");
  errors.forEach((message) => {
    const li = document.createElement("li");
    li.textContent = message;
    list.appendChild(li);
  });
  errorsEl.appendChild(list);
}

function createTripletSelect() {
  const selectEl = document.createElement("select");
  selectEl.className = "triplet-select";
  return selectEl;
}

function updateTripletRowControls(row) {
  const selects = row.querySelectorAll(".triplet-select");
  const addBtn = row.querySelector(".add-location-btn");
  const removeLocationBtn = row.querySelector(".remove-location-btn");
  const removeRowBtn = row.querySelector(".remove-triplet-btn");
  const visibilityToggle = row.querySelector(".triplet-visibility");
  const hasEnoughPoints = state.points.length >= 3;

  if (addBtn) {
    addBtn.disabled = !hasEnoughPoints;
  }
  if (removeLocationBtn) {
    removeLocationBtn.disabled = !hasEnoughPoints || selects.length <= 3;
  }
  if (removeRowBtn) {
    removeRowBtn.disabled = !hasEnoughPoints;
  }
  if (visibilityToggle) {
    visibilityToggle.disabled = !hasEnoughPoints;
  }
}

function createTripletRow(defaultIndices) {
  const row = document.createElement("div");
  row.className = "triplet-row";
  row.dataset.rowId = String(state.nextRowId);
  state.nextRowId += 1;

  const visibilityLabel = document.createElement("label");
  visibilityLabel.className = "triplet-toggle";
  const visibilityInput = document.createElement("input");
  visibilityInput.type = "checkbox";
  visibilityInput.className = "triplet-visibility";
  visibilityInput.checked = true;
  visibilityLabel.appendChild(visibilityInput);
  visibilityLabel.append("Show");
  row.appendChild(visibilityLabel);

  const selectsWrap = document.createElement("div");
  selectsWrap.className = "triplet-selects";
  row.appendChild(selectsWrap);

  for (let k = 0; k < 3; k += 1) {
    selectsWrap.appendChild(createTripletSelect());
  }

  const nearestInfo = document.createElement("span");
  nearestInfo.className = "triplet-nearest";
  row.appendChild(nearestInfo);

  const addLocationBtn = document.createElement("button");
  addLocationBtn.type = "button";
  addLocationBtn.className = "add-location-btn";
  addLocationBtn.textContent = "Add Location";
  row.appendChild(addLocationBtn);

  const removeLocationBtn = document.createElement("button");
  removeLocationBtn.type = "button";
  removeLocationBtn.className = "remove-location-btn";
  removeLocationBtn.textContent = "Remove Location";
  row.appendChild(removeLocationBtn);

  const removeBtn = document.createElement("button");
  removeBtn.type = "button";
  removeBtn.className = "remove-triplet-btn";
  removeBtn.textContent = "Remove Row";
  row.appendChild(removeBtn);

  tripletRowsEl.appendChild(row);
  populateRowOptions(row, defaultIndices);
}

function populateRowOptions(row, preferredIndices) {
  const selects = [...row.querySelectorAll(".triplet-select")];
  const defaults = preferredIndices || [0, 1, 2];
  const sortedPoints = [...state.points].sort((a, b) => a.name.localeCompare(b.name));

  selects.forEach((selectEl, idx) => {
    const oldValue = Number.parseInt(selectEl.value, 10);
    selectEl.replaceChildren();

    sortedPoints.forEach((point) => {
      const option = document.createElement("option");
      option.value = String(point.index);
      option.textContent = point.name;
      selectEl.appendChild(option);
    });

    if (!state.points.length) {
      selectEl.disabled = true;
      return;
    }

    const desired = Number.isInteger(oldValue) ? oldValue : defaults[idx] ?? idx;
    const clamped = clamp(desired, 0, state.points.length - 1);
    selectEl.value = String(clamped);
    selectEl.disabled = state.points.length < 3;
  });

  const removeBtn = row.querySelector(".remove-triplet-btn");
  if (removeBtn) {
    removeBtn.disabled = state.points.length < 3;
  }

  updateTripletRowControls(row);
}

function addLocationSelect(row) {
  const selectsWrap = row.querySelector(".triplet-selects") || row;
  selectsWrap.appendChild(createTripletSelect());
  populateRowOptions(row);
}

function removeLocationSelect(row) {
  const selectsWrap = row.querySelector(".triplet-selects") || row;
  const selects = [...selectsWrap.querySelectorAll(".triplet-select")];
  if (selects.length <= 3) {
    return;
  }
  selects[selects.length - 1].remove();
  populateRowOptions(row);
}

function refreshTripletRows() {
  const rows = [...tripletRowsEl.querySelectorAll(".triplet-row")];
  if (!rows.length && state.points.length >= 3) {
    createTripletRow([0, 1, 2]);
  } else {
    rows.forEach((row) => populateRowOptions(row));
  }

  const hasEnough = state.points.length >= 3;
  addTripletBtnEl.disabled = !hasEnough;
  plotTripletsBtnEl.disabled = !hasEnough;
  if (!hasEnough) {
    fitInfoEl.textContent = "Need at least 3 valid locations to define triplets.";
  }
}

function collectTripletSelections() {
  const rows = [...tripletRowsEl.querySelectorAll(".triplet-row")];
  const selections = [];
  const rowErrors = [];

  rows.forEach((row, idx) => {
    const values = [...row.querySelectorAll(".triplet-select")].map((selectEl) =>
      Number.parseInt(selectEl.value, 10)
    );
    const visibilityToggle = row.querySelector(".triplet-visibility");
    const visible = visibilityToggle ? visibilityToggle.checked : true;
    const rowId = row.dataset.rowId || String(idx + 1);

    if (values.some((v) => !Number.isInteger(v))) {
      rowErrors.push(`Row ${idx + 1}: invalid point selection.`);
      return;
    }

    if (values.length < 3) {
      rowErrors.push(`Row ${idx + 1}: select at least 3 locations.`);
      return;
    }

    if (new Set(values).size !== values.length) {
      rowErrors.push(`Row ${idx + 1}: locations must be distinct.`);
      return;
    }

    selections.push({ rowId, indices: values, visible });
  });

  return { selections, rowErrors };
}

function computeIntersections(circles) {
  const intersections = [];

  for (let i = 0; i < circles.length - 1; i += 1) {
    for (let j = i + 1; j < circles.length; j += 1) {
      const raw = cross3(circles[i].normal, circles[j].normal);
      const intersectionVector = normalize3(raw);
      if (!intersectionVector) {
        continue;
      }

      const opposite = [-intersectionVector[0], -intersectionVector[1], -intersectionVector[2]];
      const p1 = vectorToLatLon(intersectionVector);
      const p2 = vectorToLatLon(opposite);

      intersections.push({
        circleA: i + 1,
        circleB: j + 1,
        point1: p1,
        point2: p2
      });
    }
  }

  return intersections;
}

function renderIntersections(intersections) {
  intersectionResultsEl.replaceChildren();
  if (!intersections.length) {
    const empty = document.createElement("p");
    empty.textContent = "No pairwise intersections to show (need at least two non-parallel circles).";
    intersectionResultsEl.appendChild(empty);
    return;
  }

  const table = document.createElement("table");
  const thead = document.createElement("thead");
  const hr = document.createElement("tr");
  ["Circle Pair", "Intersection 1 (lat, lon)", "Intersection 2 (lat, lon)"].forEach((label) => {
    const th = document.createElement("th");
    th.textContent = label;
    hr.appendChild(th);
  });
  thead.appendChild(hr);

  const tbody = document.createElement("tbody");
  intersections.forEach((item) => {
    const tr = document.createElement("tr");

    const pairCell = document.createElement("td");
    pairCell.textContent = `${item.circleA} & ${item.circleB}`;
    tr.appendChild(pairCell);

    const p1Cell = document.createElement("td");
    p1Cell.className = "mono";
    p1Cell.textContent = `${formatCoord(item.point1.lat)}, ${formatCoord(item.point1.lon)}`;
    tr.appendChild(p1Cell);

    const p2Cell = document.createElement("td");
    p2Cell.className = "mono";
    p2Cell.textContent = `${formatCoord(item.point2.lat)}, ${formatCoord(item.point2.lon)}`;
    tr.appendChild(p2Cell);

    tbody.appendChild(tr);
  });

  table.appendChild(thead);
  table.appendChild(tbody);
  intersectionResultsEl.appendChild(table);
}

function getTripletLabel(circle, index) {
  const labelIndex = index + 1;
  return `Triplet ${labelIndex}: ${circle.names.join(" | ")}`;
}

function refreshIntersectionSelectors() {
  if (!intersectionAEl || !intersectionBEl) {
    return;
  }
  const circles = state.plottedTriplets;
  const previousA = intersectionAEl.value;
  const previousB = intersectionBEl.value;

  intersectionAEl.replaceChildren();
  intersectionBEl.replaceChildren();

  if (circles.length < 2) {
    const option = document.createElement("option");
    option.value = "";
    option.textContent = "Plot at least two rows";
    intersectionAEl.appendChild(option);
    intersectionBEl.appendChild(option.cloneNode(true));
    intersectionAEl.disabled = true;
    intersectionBEl.disabled = true;
    if (intersectionCalcEl) {
      intersectionCalcEl.disabled = true;
    }
    if (intersectionSelectedEl) {
      intersectionSelectedEl.textContent = "";
    }
    return;
  }

  circles.forEach((circle, idx) => {
    const label = getTripletLabel(circle, idx);
    const optionA = document.createElement("option");
    optionA.value = String(idx);
    optionA.textContent = label;
    intersectionAEl.appendChild(optionA);

    const optionB = document.createElement("option");
    optionB.value = String(idx);
    optionB.textContent = label;
    intersectionBEl.appendChild(optionB);
  });

  intersectionAEl.disabled = false;
  intersectionBEl.disabled = false;
  if (intersectionCalcEl) {
    intersectionCalcEl.disabled = false;
  }

  if (previousA && intersectionAEl.querySelector(`option[value="${previousA}"]`)) {
    intersectionAEl.value = previousA;
  }
  if (previousB && intersectionBEl.querySelector(`option[value="${previousB}"]`)) {
    intersectionBEl.value = previousB;
  }
}

function renderSelectedIntersection(circleA, circleB, indexA, indexB) {
  if (!intersectionSelectedEl) {
    return;
  }
  const raw = cross3(circleA.normal, circleB.normal);
  const intersectionVector = normalize3(raw);
  if (!intersectionVector) {
    intersectionSelectedEl.textContent =
      `Triplet ${indexA + 1} and Triplet ${indexB + 1} are parallel (no intersection).`;
    return;
  }

  const opposite = [-intersectionVector[0], -intersectionVector[1], -intersectionVector[2]];
  const p1 = vectorToLatLon(intersectionVector);
  const p2 = vectorToLatLon(opposite);
  intersectionSelectedEl.textContent =
    `Intersection points: (${formatCoord(p1.lat)}, ${formatCoord(p1.lon)}) ` +
    `and (${formatCoord(p2.lat)}, ${formatCoord(p2.lon)}).`;
}

function getVisibleTripletOverlays() {
  return state.plottedTriplets.filter((circle) => circle.visible);
}

function refreshTripletSummary(intersectionsCount) {
  const visibleCount = getVisibleTripletOverlays().length;
  summaryEl.textContent =
    `Valid locations: ${state.points.length}. ` +
    `Triplet circles plotted: ${state.plottedTriplets.length}. ` +
    `Visible triplet circles: ${visibleCount}. ` +
    `Pairwise circle intersections: ${intersectionsCount}.`;
  fitInfoEl.textContent =
    `Showing ${visibleCount} of ${state.plottedTriplets.length} plotted circle` +
    `${state.plottedTriplets.length === 1 ? "" : "s"}.`;
}

function refreshManualTripletOverlays() {
  const visibleCircles = getVisibleTripletOverlays();
  const intersections = computeIntersections(visibleCircles);
  refreshMapAndLegend();
  renderIntersections(intersections);
  if (state.plottedTriplets.length) {
    refreshTripletSummary(intersections.length);
  }
  refreshIntersectionSelectors();
}

function updateBestNSummary() {
  if (!bestNSummaryEl) {
    return;
  }
  if (!state.bestNOverlays.length) {
    bestNSummaryEl.textContent = "";
    return;
  }
  bestNSummaryEl.textContent =
    `Showing ${state.bestNOverlays.length} best-fit circle` +
    `${state.bestNOverlays.length === 1 ? "" : "s"} ` +
    "ranked by total distance to all points.";
}

function computeBestNOverlays(requestedN) {
  if (state.points.length < 2 || !state.pairCandidates.length) {
    return [];
  }
  const limit = clamp(Math.round(requestedN), 1, state.pairCandidates.length);
  const ranked = state.pairCandidates.map((pair) => ({
    normal: pair.normal,
    totalDistanceMiles: totalDistanceToGreatCircleMiles(pair.normal)
  }));
  ranked.sort((a, b) => a.totalDistanceMiles - b.totalDistanceMiles);
  return ranked.slice(0, limit).map((item, idx) => ({
    normal: item.normal,
    indices: [],
    names: [],
    totalDistanceMiles: item.totalDistanceMiles,
    color: OVERLAY_COLORS[(idx + 4) % OVERLAY_COLORS.length]
  }));
}

function updateTripletRowNearestInfo(circles) {
  circles.forEach((circle) => {
    const row = tripletRowsEl.querySelector(`.triplet-row[data-row-id="${circle.rowId}"]`);
    if (!row) {
      return;
    }
    const infoEl = row.querySelector(".triplet-nearest");
    if (!infoEl) {
      return;
    }

    if (!circle.closestUnadded) {
      infoEl.textContent = "No unadded locations.";
      return;
    }

    infoEl.textContent =
      `Closest unadded: ${circle.closestUnadded.name} ` +
      `(${circle.closestUnadded.distance.toFixed(2)} mi)`;
  });
}

function plotTriplets() {
  if (state.points.length < 3) {
    fitInfoEl.textContent = "Need at least 3 valid locations to plot triplets.";
    return;
  }

  const { selections, rowErrors } = collectTripletSelections();
  if (rowErrors.length) {
    fitInfoEl.textContent = rowErrors.join(" ");
    return;
  }

  if (!selections.length) {
    fitInfoEl.textContent = "Add at least one row before plotting.";
    return;
  }

  const circles = [];
  const fitErrors = [];
  selections.forEach((selection, idx) => {
    const fit = computeBestFitGreatCircle(selection.indices);
    if (!fit) {
      fitErrors.push(`Row ${idx + 1}: failed to compute stable great circle.`);
      return;
    }

    const closest = computeClosestUnaddedPoint(fit.normal, selection.indices);
    circles.push({
      ...fit,
      rowId: selection.rowId,
      visible: selection.visible,
      closestUnadded: closest ? { name: closest.point.name, distance: closest.distance } : null,
      color: OVERLAY_COLORS[idx % OVERLAY_COLORS.length]
    });
  });

  if (fitErrors.length) {
    fitInfoEl.textContent = fitErrors.join(" ");
    return;
  }

  state.plottedTriplets = circles;
  updateTripletRowNearestInfo(circles);
  refreshManualTripletOverlays();
}

function run() {
  const { points, errors } = parseLocations(textarea.value);
  state.points = points;
  state.pairCandidates = points.length >= 2 ? buildPairCandidates() : [];
  state.pairSetRows = [];
  state.qualifyingPairCount = 0;
  state.plottedTriplets = [];
  state.bestNOverlays = [];
  state.tripletCandidates = points.length >= 3 ? buildTripletCandidates() : [];
  state.showCutoffCircles = plotCutoffCirclesEl.checked;
  state.userTouchedCutoff = false;
  state.cutoffMiles = 10;
  state.userTouchedMinLocations = false;
  state.minLocations = 3;
  state.globeUserControlled = false;
  state.globeCenter = null;

  renderErrors(errors);
  refreshTripletRows();
  configureCutoffControls();
  configureMinLocationsControls();

  summaryEl.textContent = `Valid locations loaded: ${points.length}.`;
  updateBestNSummary();
  intersectionResultsEl.replaceChildren();
  if (points.length >= 3) {
    fitInfoEl.textContent = "Add one or more triplets and click \"Plot Triplets\".";
  }

  applyTripletCutoffAndRenderTable();
}

form.addEventListener("submit", (event) => {
  event.preventDefault();
  run();
});

cutoffRangeEl.addEventListener("input", () => {
  state.userTouchedCutoff = true;
  setCutoffValue(Number(cutoffRangeEl.value));
  applyTripletCutoffAndRenderTable();
});

cutoffInputEl.addEventListener("input", () => {
  state.userTouchedCutoff = true;
  const parsed = Number(cutoffInputEl.value);
  if (!Number.isFinite(parsed)) {
    return;
  }
  setCutoffValue(parsed);
  applyTripletCutoffAndRenderTable();
});

cutoffInputEl.addEventListener("change", () => {
  const parsed = Number(cutoffInputEl.value);
  setCutoffValue(Number.isFinite(parsed) ? parsed : state.cutoffMiles);
  applyTripletCutoffAndRenderTable();
});

minLocationsRangeEl.addEventListener("input", () => {
  state.userTouchedMinLocations = true;
  setMinLocationsValue(Number(minLocationsRangeEl.value));
  applyTripletCutoffAndRenderTable();
});

minLocationsInputEl.addEventListener("input", () => {
  state.userTouchedMinLocations = true;
  const parsed = Number(minLocationsInputEl.value);
  if (!Number.isFinite(parsed)) {
    return;
  }
  setMinLocationsValue(parsed);
  applyTripletCutoffAndRenderTable();
});

minLocationsInputEl.addEventListener("change", () => {
  const parsed = Number(minLocationsInputEl.value);
  setMinLocationsValue(Number.isFinite(parsed) ? parsed : state.minLocations);
  applyTripletCutoffAndRenderTable();
});

plotCutoffCirclesEl.addEventListener("change", () => {
  state.showCutoffCircles = plotCutoffCirclesEl.checked;
  refreshMapAndLegend();
});

addTripletBtnEl.addEventListener("click", () => {
  if (state.points.length < 3) {
    return;
  }
  createTripletRow([0, 1, 2]);
});

tripletRowsEl.addEventListener("click", (event) => {
  const target = event.target;
  if (!(target instanceof HTMLElement)) {
    return;
  }

  if (target.classList.contains("add-location-btn")) {
    const row = target.closest(".triplet-row");
    if (row) {
      addLocationSelect(row);
    }
    return;
  }

  if (target.classList.contains("remove-location-btn")) {
    const row = target.closest(".triplet-row");
    if (row) {
      removeLocationSelect(row);
    }
    return;
  }

  if (!target.classList.contains("remove-triplet-btn")) {
    return;
  }

  const rows = [...tripletRowsEl.querySelectorAll(".triplet-row")];
  if (rows.length <= 1) {
    return;
  }

  const row = target.closest(".triplet-row");
  if (row) {
    row.remove();
    const rowId = row.dataset.rowId;
    if (rowId && state.plottedTriplets.length) {
      state.plottedTriplets = state.plottedTriplets.filter((circle) => circle.rowId !== rowId);
      refreshManualTripletOverlays();
    }
  }
});

tripletRowsEl.addEventListener("change", (event) => {
  const target = event.target;
  if (!(target instanceof HTMLElement)) {
    return;
  }

  if (!target.classList.contains("triplet-visibility")) {
    return;
  }

  const row = target.closest(".triplet-row");
  if (!row) {
    return;
  }

  const rowId = row.dataset.rowId;
  if (!rowId) {
    return;
  }

  const overlay = state.plottedTriplets.find((circle) => circle.rowId === rowId);
  if (overlay) {
    overlay.visible = target.checked;
    refreshManualTripletOverlays();
  }
});

plotTripletsBtnEl.addEventListener("click", () => {
  plotTriplets();
});

if (generateWordCirclesBtnEl) {
  generateWordCirclesBtnEl.addEventListener("click", () => {
    generateWordCirclesFromInputs();
  });
}

let globeDragging = false;
let globeLastPointer = null;

function stopGlobeDrag(pointerId) {
  globeDragging = false;
  globeLastPointer = null;
  if (globeSvgEl) {
    globeSvgEl.classList.remove("globe-dragging");
    if (pointerId != null && globeSvgEl.hasPointerCapture(pointerId)) {
      globeSvgEl.releasePointerCapture(pointerId);
    }
  }
}

if (globeSvgEl) {
  globeSvgEl.addEventListener("pointerdown", (event) => {
    globeDragging = true;
    globeLastPointer = { x: event.clientX, y: event.clientY };
    globeSvgEl.classList.add("globe-dragging");
    globeSvgEl.setPointerCapture(event.pointerId);
  });

  globeSvgEl.addEventListener("pointermove", (event) => {
    if (!globeDragging || !globeLastPointer) {
      return;
    }
    const dx = event.clientX - globeLastPointer.x;
    const dy = event.clientY - globeLastPointer.y;
    globeLastPointer = { x: event.clientX, y: event.clientY };

    const degPerPixel = 180 / (Math.PI * GLOBE_RADIUS);
    const center = getGlobeCenter(state.points);
    const nextLat = clamp(center.lat - dy * degPerPixel, -89, 89);
    const nextLon = wrapLongitude(center.lon - dx * degPerPixel);
    setGlobeCenter(nextLat, nextLon, true);
    refreshGlobeOnly();
  });

  globeSvgEl.addEventListener("pointerup", (event) => {
    stopGlobeDrag(event.pointerId);
  });
  globeSvgEl.addEventListener("pointercancel", (event) => {
    stopGlobeDrag(event.pointerId);
  });
  globeSvgEl.addEventListener("pointerleave", (event) => {
    stopGlobeDrag(event.pointerId);
  });
}

if (globeResetBtnEl) {
  globeResetBtnEl.addEventListener("click", () => {
    state.globeUserControlled = false;
    state.globeCenter = null;
    refreshGlobeOnly();
  });
}

if (globeLabelsToggleEl) {
  globeLabelsToggleEl.addEventListener("change", () => {
    refreshGlobeOnly();
  });
}

if (intersectionCalcEl) {
  intersectionCalcEl.addEventListener("click", () => {
    const indexA = Number.parseInt(intersectionAEl.value, 10);
    const indexB = Number.parseInt(intersectionBEl.value, 10);
    if (!Number.isInteger(indexA) || !Number.isInteger(indexB)) {
      return;
    }
    if (indexA === indexB) {
      if (intersectionSelectedEl) {
        intersectionSelectedEl.textContent = "Pick two different triplet lines.";
      }
      return;
    }
    const circleA = state.plottedTriplets[indexA];
    const circleB = state.plottedTriplets[indexB];
    if (!circleA || !circleB) {
      return;
    }
    renderSelectedIntersection(circleA, circleB, indexA, indexB);
  });
}

run();
