-- Prove2me | Theorems.Thm_StrategicPolicy_NonMonotone_optimal_family
-- name    : StrategicPolicy.NonMonotone.optimal_family
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T14:40:25.139066+00:00
-- url     : https://prove2.me/theorems/121acbc9-f482-4536-9c24-c1a56c04364e
-- title:
--   Section 5, p. 9 — every policy in the printed family is optimal and moves mass from x₂ to x₁
-- statement:
--   Let $\pi$ be a policy for the fixed three-value instance. If $\pi(x_1)=1$, $\pi(x_2)\leq0.7$, and $\pi(x_3)=1$, then
--
--   $$
--   u(\pi,0.1)\geq u(\rho,0.1)\quad\text{for every admissible policy }\rho,
--   \qquad \operatorname{br}_{c,q,\pi}(x_2)=x_1.
--   $$
--
--   Thus the entire family printed in Section 5 attains the optimal utility, and the mass initially at $x_2$ is transported to $x_1$.
--
--   **Formalization Note** The bound includes $\pi(x_2)=0.7$. At this endpoint the individual at $x_2$ is indifferent in benefit less cost between staying and moving to $x_1$; the paper's highest-outcome tie rule selects $x_1$.
-- source:
--   Tsirtsis et al., Optimal Decision Making Under Strategic Behavior, arXiv:1905.09239v5, p. 9, §5 example after the general-cost matrix

import Mathlib
import Definitions.Def_StrategicPolicy_NonMonotone_Setting
import Definitions.Def_StrategicPolicy_NonMonotone_Example

namespace StrategicPolicy.NonMonotone

/-- Section 5, page 9: each policy in the printed family is optimal and moves the second mass to the first feature. -/
theorem optimal_family (π : Fin 3 → ℝ) (hπ : π ∈ StrategicPolicy.MonotoneBinary.Policies 3)
    (h0 : π 0 = 1) (h1 : π 1 ≤ 7 / 10) (h2 : π 2 = 1) :
    IsMaxOn (StrategicPolicy.MonotoneBinary.u p q γ c) (StrategicPolicy.MonotoneBinary.Policies 3) π ∧ br c q π 1 = 0 := by sorry

end StrategicPolicy.NonMonotone
