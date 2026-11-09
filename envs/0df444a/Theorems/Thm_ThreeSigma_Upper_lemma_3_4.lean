-- Prove2me | Theorems.Thm_ThreeSigma_Upper_lemma_3_4
-- name    : ThreeSigma.Upper.lemma_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:37:13.814126+00:00
-- url     : https://prove2.me/theorems/4f777364-a6be-4a70-b07d-e7ea5c8d6c93
-- title:
--   Lemma 3.4 — capped trace
-- statement:
--   Let $a_1,\ldots,a_m\in\mathbb R^n$ be arbitrary real rows and let $V\subseteq\mathbb R^n$ be a linear subspace. If
--   $$\sum_{i=1}^m\langle a_i,v\rangle^2\ge\|v\|_2^2\qquad(v\in V),$$
--   then
--   $$\dim V\le\sum_{i=1}^m\min\{\|a_i\|_2^2,1\}.$$
--   The lemma converts domination of a quadratic form on a subspace into a dimension bound. Zero rows, the zero subspace, and empty coordinate families are included.
--
--   Differences from the source:
--   - encoding: vectors in ℝⁿ with coordinates indexed 1 through n → EuclideanSpace ℝ (Fin n) with coordinates indexed 0 through n−1; reason: canonical isometric coordinate representation; no instances are excluded
--   - encoding: dimension as an integer compared with a real sum → Module.finrank ℝ V cast to ℝ; reason: the ambient space is finite dimensional, so this is precisely its real dimension
-- source:
--   Victor Reis, Zhao Song, Three Standard Deviations Suffice While One Does Not, STOC 2027 submission #393 (October 2026), Lemma 3.4, pp. 6–7; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/393.pdf

import Mathlib

namespace ThreeSigma.Upper

/-- Lemma 3.4 (capped trace), without restrictions on rows or subspace. -/
theorem lemma_3_4 {m n : ℕ} (a : Fin m → EuclideanSpace ℝ (Fin n))
    (V : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (hV : ∀ v ∈ V, ‖v‖ ^ 2 ≤ ∑ i, (inner ℝ (a i) v) ^ 2) :
    (Module.finrank ℝ V : ℝ) ≤ ∑ i, min (‖a i‖ ^ 2) (1 : ℝ) := by sorry

end ThreeSigma.Upper
