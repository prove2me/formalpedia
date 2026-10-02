-- Prove2me | Theorems.Thm_StarShapedRisk_Representation_convex_normalized_superhomogeneous
-- name    : StarShapedRisk.Representation.convex_normalized_superhomogeneous
-- status  : Proved
-- author  : @junyihjy
-- created : 2026-10-01T11:38:48.296323+00:00
-- url     : https://prove2.me/theorems/bd79ccf9-5c4b-4f27-9b65-30c251d7689b
-- title:
--   A convex normalized function is positively superhomogeneous (star-shaped)
-- statement:
--   A convex real function with f(0) = 0 is positively superhomogeneous: for every t > 1 and every X, f(tX) >= t f(X). Proof: X = (1/t)(tX) + (1-1/t)0, so convexity and f(0)=0 give f(X) <= (1/t) f(tX). This is the elementary step in Castagnoli et al. (2022) showing every convex risk measure is star-shaped (used in Theorem 2's (ii)=>(i) direction).

import Mathlib

namespace StarShapedRisk.Representation

/-- Castagnoli et al. (2022), used in the proof of Theorem 2 (p. 2644): a convex
    function with `f 0 = 0` is positively superhomogeneous ("star-shaped"): for
    `t > 1`, `t * f X ≤ f (t • X)`. Proof: `X = (1/t) • (t • X) +
    (1 - 1/t) • 0`, so convexity and `f 0 = 0` give
    `f X ≤ (1/t) * f (t • X)`. This is the step showing every convex
    risk measure is star-shaped, feeding Theorem 2's `(ii) ⇒ (i)` via
    Theorem 1's infimum case. -/
theorem convex_normalized_superhomogeneous {E : Type*} [AddCommGroup E] [Module ℝ E]
    (f : E → ℝ) (hconv : ConvexOn ℝ Set.univ f) (h0 : f 0 = 0)
    {t : ℝ} (ht : 1 < t) (X : E) :
    t * f X ≤ f (t • X) := by
  sorry

end StarShapedRisk.Representation
