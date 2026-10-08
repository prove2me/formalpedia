-- Prove2me | Theorems.Thm_SelfScaledLongStep_PrimalDual_proposition_4_1
-- name    : SelfScaledLongStep.PrimalDual.proposition_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T12:21:33.883395+00:00
-- url     : https://prove2.me/theorems/659be081-b206-4487-ad12-8c2db701b878
-- title:
--   Proposition 4.1, p. 17 — τ − ln(1 + τ) increasing on τ ≥ 0; (τ − ln(1 + τ))/τ² decreasing; (−τ − ln(1 − τ))/τ² increasing
-- statement:
--   1. On $\tau\ge0$ the function $\tau-\ln(1+\tau)$ is increasing.
--   2. On $\tau>-1$ the function
--   $$\frac{\tau-\ln(1+\tau)}{\tau^2}\qquad(\text{defined as }1/2\text{ at }\tau=0)$$
--   is decreasing.
--   3. On $\tau<1$ the function
--   $$\frac{-\tau-\ln(1-\tau)}{\tau^2}\qquad(\text{defined as }1/2\text{ at }\tau=0)$$
--   is increasing.
--
--   These elementary facts are used together with (4.8) to turn bounds on step lengths into guaranteed decreases of a potential function.
--
--   **Formalization Note** "Monotonically increasing/decreasing" is formalized as strict monotonicity (`StrictMonoOn`, `StrictAntiOn`) on the stated intervals; all three functions are strictly monotone there, and the strict form implies the weak one, so the statement is not weaker than the page. The value $1/2$ at $\tau=0$ is written as an `if`. The proposition is pure real analysis, so it carries none of the cone and barrier binders of the other items.
-- source:
--   Nesterov & Todd, Self-scaled barriers and interior-point methods for convex programming, Math. Oper. Res. 22(1) (1997) 1–42, p. 17, Proposition 4.1

import Mathlib

namespace SelfScaledLongStep.PrimalDual

/-- **Proposition 4.1** (p. 17), "monotonically" read strictly (which implies the weak reading).
(i) `τ ↦ τ − ln(1 + τ)` is increasing on `τ ≥ 0`.
(ii) `τ ↦ (τ − ln(1 + τ))/τ²` (`1/2` at `τ = 0`) is decreasing on `τ > −1`.
(iii) `τ ↦ (−τ − ln(1 − τ))/τ²` (`1/2` at `τ = 0`) is increasing on `τ < 1`. -/
theorem proposition_4_1 :
    StrictMonoOn (fun τ : ℝ => τ - Real.log (1 + τ)) (Set.Ici 0) ∧
    StrictAntiOn (fun τ : ℝ => if τ = 0 then 1 / 2 else (τ - Real.log (1 + τ)) / τ ^ 2)
      (Set.Ioi (-1)) ∧
    StrictMonoOn (fun τ : ℝ => if τ = 0 then 1 / 2 else (-τ - Real.log (1 - τ)) / τ ^ 2)
      (Set.Iio 1) := by sorry

end SelfScaledLongStep.PrimalDual
