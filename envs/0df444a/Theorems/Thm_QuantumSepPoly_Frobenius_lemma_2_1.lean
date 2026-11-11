-- Prove2me | Theorems.Thm_QuantumSepPoly_Frobenius_lemma_2_1
-- name    : QuantumSepPoly.Frobenius.lemma_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:09:52.983389+00:00
-- url     : https://prove2.me/theorems/3a6330a5-da55-40e1-b5dd-adf73a5542d2
-- title:
--   Lemma 2.1 — Complex Gaussian inverse moment
-- statement:
--   Let $X$ be a standard complex Gaussian vector in $\mathbb C^d$ and $Y=\|X\|_2^2$. For every integer $q$ with $1\le q\le d/4$,
--   $$\|Y^{-1}\|_{L^{2q}}\le 2/d.$$
--   This fixes the inverse-moment normalization used in the Haar estimates.
--
--   Differences from the source:
--   - encoding: coordinates labelled 1 through d → coordinates indexed by Fin d from 0 through d-1; reason: canonical relabelling preserves all vectors, matrices, sums, and constraints
--   - encoding: finite L^(2q) inverse-moment bound with arbitrary value at X=0 → nonnegative extended-real Lebesgue moment, with inverse zero at X=0; reason: equivalent finite-moment statement; no nonintegrable Bochner default is possible
-- source:
--   Giulio Malavolta, STOC 2027 submission #1577 (October 2026), Lemma 2.1, p. 7 (PDF p. 7); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1577.pdf

import Definitions.Def_QuantumSepPoly_Frobenius_Gaussian

open MeasureTheory

namespace QuantumSepPoly.Frobenius

/-- Lemma 2.1, p.7. Inversion at the null input is explicitly zero. -/
theorem lemma_2_1 (d q : ℕ) (hq : 1 ≤ q) (hqd : 4*q ≤ d) :
  Lq (realGaussian d) (2*q) (fun g => (vecSq (complexGaussian g))⁻¹) ≤
    ENNReal.ofReal (2 / (d : ℝ)) := by sorry

end QuantumSepPoly.Frobenius
