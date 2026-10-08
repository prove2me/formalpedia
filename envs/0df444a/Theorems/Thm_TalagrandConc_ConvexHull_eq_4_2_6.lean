-- Prove2me | Theorems.Thm_TalagrandConc_ConvexHull_eq_4_2_6
-- name    : TalagrandConc.ConvexHull.eq_4_2_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:42:15.856632+00:00
-- url     : https://prove2.me/theorems/b96116ad-f191-456a-887e-a9a4faeb0e80
-- title:
--   Eq. (4.2.6) — $P(A_t^c)\ge1-P(A)^{-\alpha}\exp\big(-\frac{\alpha t^2}{2(\alpha+1)}\big)$
-- statement:
--   Let $(\Omega,\mu)$ be a probability space and $P=\mu^{\otimes N}$ on $\Omega^N$. Let $\alpha>0$, $t\ge0$, $A\subseteq\Omega^N$, and let $A_t^c=\{x;\ f_c(A,x)\le t\}$ be the convex-hull enlargement of $A$. Then
--   $$P(A_t^c)\ge1-\frac{1}{P(A)^{\alpha}}\exp\Big(-\frac{\alpha t^2}{2(\alpha+1)}\Big).$$
--
--   This generalizes the tail bound (4.1.3), $P(A_t^c)\ge1-P(A)^{-1}e^{-t^2/4}$, which is the case $\alpha=1$; optimizing over $\alpha$ gives Corollary 4.2.5.
--
--   **Formalization Note** $A$ and $x\mapsto f_\alpha(A,x)$ are assumed measurable (the paper's convention of pp. 81–82). $P(A_t^c)$ is Lean's measure of an arbitrary set, i.e. its outer probability, as the paper prescribes when measurability fails. The bound is computed in $[0,\infty]$ with truncated subtraction, so a negative right-hand side reads as $0$, and $P(A)^{-\alpha}=+\infty$ when $P(A)=0$. $t\ge0$ is assumed (for $t<0$, $A_t^c=\varnothing$ and the paper does not use the enlargement).
-- source:
--   Talagrand, Concentration of measure and isoperimetric inequalities in product spaces, Publ. Math. IHÉS 81 (1995), p. 128, Eq. (4.2.6)

import Mathlib
import Definitions.Def_TalagrandConc_ConvexHull_Basic

namespace TalagrandConc.ConvexHull

open MeasureTheory
open scoped ENNReal

/-- Talagrand (1995), p. 128, Eq. (4.2.6): for `α > 0`, `t ≥ 0` and `A ⊆ Ω^N`,
`P(A_t^c) ≥ 1 − P(A)^{−α} exp(−α t² / (2(α + 1)))`.
Measurability convention (p. 81–82): `A` and `x ↦ f_α(A, x)` are assumed measurable; `P(A_t^c)`
is Lean's measure of an arbitrary set, i.e. the outer probability. The right side is in `ℝ≥0∞`
(truncated subtraction: a negative bound reads as `0`). -/
theorem eq_4_2_6 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (N : ℕ) (α : ℝ) (hα : 0 < α) (A : Set (Fin N → Ω)) (hA : MeasurableSet A)
    (hmeas : Measurable fun x => fAlpha α A x) (t : ℝ) (ht : 0 ≤ t) :
    1 - (Measure.pi (fun _ : Fin N => μ) A) ^ (-α) *
          ENNReal.ofReal (Real.exp (-(α * t ^ 2 / (2 * (α + 1)))))
      ≤ Measure.pi (fun _ : Fin N => μ) (enlarge A t) := by sorry

end TalagrandConc.ConvexHull
