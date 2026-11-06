-- Prove2me | Theorems.Thm_UCalibDirichlet_lemma_D_3
-- name    : UCalibDirichlet.lemma_D_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:24:11.560131+00:00
-- url     : https://prove2.me/theorems/04951174-41b6-4597-84e9-d92d93e8fb0c
-- title:
--   Lemma D.3 — $x\mapsto xf'(x)-f(x)$ is non-decreasing for convex $f$
-- statement:
--   Let $f:[0,1]\to\mathbb R$ be convex. Then
--   $$h(x)=xf'(x)-f(x)$$
--   is non-decreasing.
--
--   Combined with Chebyshev's sum inequality it gives the upper bound of the stability lemma (Lemma 1.6).
--
--   Differences from the source:
--   - encoding: h on [0,1] with f′(x) → h monotone on {x ∈ (0,1) : f differentiable at x}; reason: f′(x) exists only at points of differentiability (all but countably many of (0,1)); a function on [0,1] has no two-sided derivative at 0 or 1
-- source:
--   Frongillo, Luo, Mehta & Schneider, Near-Optimal Regret in U-Calibration for Every Proper Loss (manuscript, STOC 2027 submission), Lemma D.3, p.37

import Mathlib

namespace UCalibDirichlet

/-- **Lemma D.3.** Frongillo, Luo, Mehta & Schneider (manuscript, STOC 2027 submission), Lemma D.3,
p.37: "Let `f : [0, 1] → ℝ` be convex. Then `h(x) = xf′(x) − f(x)` is non-decreasing."

**Formalization Note.** `f : ℝ → ℝ` convex on `[0, 1]`. `f′(x)` is the derivative, which exists at
all but countably many points of `(0, 1)`; the monotonicity is asserted on the set of points
`x ∈ (0, 1)` at which `f` is differentiable (at the endpoints of `[0, 1]` a function on `[0, 1]` has
no two-sided derivative). -/
theorem lemma_D_3 (f : ℝ → ℝ) (hf : ConvexOn ℝ (Set.Icc 0 1) f) :
    MonotoneOn (fun x => x * deriv f x - f x)
      {x | x ∈ Set.Ioo (0 : ℝ) 1 ∧ DifferentiableAt ℝ f x} := by sorry

end UCalibDirichlet
