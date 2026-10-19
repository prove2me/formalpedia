-- Prove2me | Theorems.Thm_StrategicPolicy_NonMonotone_no_outcome_monotonic_optimum
-- name    : StrategicPolicy.NonMonotone.no_outcome_monotonic_optimum
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T14:40:19.402403+00:00
-- url     : https://prove2.me/theorems/ea6471d9-5e14-4cab-bde3-620432e0cc11
-- title:
--   Section 5, p. 9 — no optimal policy in the three-value general-cost instance is outcome monotonic
-- statement:
--   For the fixed three-value instance of Section 5, at least one admissible optimal policy exists, but every admissible policy maximizing the strategic utility fails outcome monotonicity:
--
--   $$
--   \bigl(\exists\pi\in[0,1]^3:\ u(\pi,0.1)=\max_{\rho\in[0,1]^3}u(\rho,0.1)\bigr)
--   \quad\land\quad
--   \bigl(\forall\pi\in[0,1]^3:\ u(\pi,0.1)=\max_{\rho\in[0,1]^3}u(\rho,0.1)
--   \Longrightarrow \neg\operatorname{OMPolicy}(q,\pi)\bigr).
--   $$
--
--   This gives the paper's counterexample to the existence of an outcome-monotonic optimum under general costs. The existence clause makes the counterexample substantive.
--
--   **Formalization Note** Outcome monotonicity uses the one-way reading of equation (1), $\pi(x_i)<\pi(x_j)\Rightarrow q(x_i)<q(x_j)$. Consequently the negative conclusion is stronger than failure of the literal biconditional printed there. The maximum is taken over all real-valued policies in $[0,1]^3$, not a finite grid.
-- source:
--   Tsirtsis et al., Optimal Decision Making Under Strategic Behavior, arXiv:1905.09239v5, p. 9, §5 bold heading and general-cost example

import Mathlib
import Definitions.Def_StrategicPolicy_NonMonotone_Setting
import Definitions.Def_StrategicPolicy_NonMonotone_Example

namespace StrategicPolicy.NonMonotone

/-- Section 5, page 9: an optimum exists, and none obeys outcome monotonicity. -/
theorem no_outcome_monotonic_optimum :
    (∃ π : Fin 3 → ℝ, π ∈ StrategicPolicy.MonotoneBinary.Policies 3 ∧ IsMaxOn (StrategicPolicy.MonotoneBinary.u p q γ c) (StrategicPolicy.MonotoneBinary.Policies 3) π) ∧
    (∀ π : Fin 3 → ℝ, π ∈ StrategicPolicy.MonotoneBinary.Policies 3 → IsMaxOn (StrategicPolicy.MonotoneBinary.u p q γ c) (StrategicPolicy.MonotoneBinary.Policies 3) π →
      ¬ StrategicPolicy.MonotoneBinary.OMPolicy q π) := by sorry

end StrategicPolicy.NonMonotone
