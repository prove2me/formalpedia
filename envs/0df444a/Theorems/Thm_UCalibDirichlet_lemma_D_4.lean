-- Prove2me | Theorems.Thm_UCalibDirichlet_lemma_D_4
-- name    : UCalibDirichlet.lemma_D_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:24:27.953554+00:00
-- url     : https://prove2.me/theorems/ebb58091-555d-42d4-9936-7aa12a0620a1
-- title:
--   Lemma D.4 — $x\mapsto f(x)+(1-x)f'(x)$ is non-decreasing for convex $f$
-- statement:
--   Let $f:[0,1]\to\mathbb R$ be convex. Then
--   $$h(x)=f(x)+(1-x)f'(x)$$
--   is non-decreasing.
--
--   It gives the nonnegativity of the stability term in Lemma 1.6.
--
--   Differences from the source:
--   - reading: h(y) = f(x) + (1 − x)f′(x) → h(x) = f(x) + (1 − x)f′(x); reason: the printed h(y) is a slip: the function depends on x only, and the proof of Lemma 1.6 (p.12) uses x ↦ f(x) + (1 − x)f′(x)
--   - encoding: h on [0,1] with f′(x) → h monotone on {x ∈ (0,1) : f differentiable at x}; reason: f′(x) exists only at points of differentiability; no two-sided derivative at 0 or 1
-- source:
--   Frongillo, Luo, Mehta & Schneider, Near-Optimal Regret in U-Calibration for Every Proper Loss (manuscript, STOC 2027 submission), Lemma D.4, p.37

import Mathlib

namespace UCalibDirichlet

/-- **Lemma D.4.** Frongillo, Luo, Mehta & Schneider (manuscript, STOC 2027 submission), Lemma D.4,
p.37: "Let `f : [0, 1] → ℝ` be convex. Then `h(y) = f(x) + (1 − x)f′(x)` is non-decreasing."

The printed `h(y)` is a slip for `h(x)`: the function is `x ↦ f(x) + (1 − x)f′(x)` (its proof and
its use in the proof of Lemma 1.6, p.12, treat it as a function of `x`).

**Formalization Note.** `f : ℝ → ℝ` convex on `[0, 1]`; monotonicity on the points `x ∈ (0, 1)`
where `f` is differentiable, as in Lemma D.3. -/
theorem lemma_D_4 (f : ℝ → ℝ) (hf : ConvexOn ℝ (Set.Icc 0 1) f) :
    MonotoneOn (fun x => f x + (1 - x) * deriv f x)
      {x | x ∈ Set.Ioo (0 : ℝ) 1 ∧ DifferentiableAt ℝ f x} := by sorry

end UCalibDirichlet
