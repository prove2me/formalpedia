-- Prove2me | Theorems.Thm_StrategicPolicy_MonotoneBinary_proposition_2
-- name    : StrategicPolicy.MonotoneBinary.proposition_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T12:59:43.494485+00:00
-- url     : https://prove2.me/theorems/3f959317-ed55-4a67-a2ec-648356b17704
-- title:
--   Proposition 2, p. 6 — an outcome monotonic optimum exists
-- statement:
--   Let $\pi^*$ maximize the utility $u(\pi,\gamma)$ among all policies $\pi\in[0,1]^m$. If the cost is outcome monotonic, there is an outcome monotonic policy $\pi$ with the same utility:
--
--   $$\pi\in[0,1]^m,\qquad \pi_i<\pi_j\Rightarrow q_i<q_j,\qquad u(\pi,\gamma)=u(\pi^*,\gamma).$$
--
--   This narrows the search for an optimum and is the prerequisite used in Theorem 3.
--
--   **Formalization Note** Optimality of $\pi^*$ is an explicit hypothesis, as in the paper. The finite model assumes distinct outcomes, free staying, and the standing positive cost condition; §4 cost monotonicity uses distinct indices. The policy monotonicity implication is the disclosed reading of (1).
-- source:
--   Tsirtsis et al., Optimal Decision Making Under Strategic Behavior, arXiv:1905.09239v5, p. 6, Proposition 2; proof p. 18, Appendix A.2

import Mathlib
import Definitions.Def_StrategicPolicy_MonotoneBinary_Setting

namespace StrategicPolicy.MonotoneBinary

variable {m : ℕ}

theorem proposition_2 [NeZero m]
    (p q : Fin m → ℝ) (γ : ℝ) (c : Fin m → Fin m → ℝ)
    (hstanding : Standing p q γ c) (hcost : OMCost q c)
    (πstar : Fin m → ℝ) (hopt : Optimal p q γ c πstar) :
    ∃ π ∈ Policies m, OMPolicy q π ∧ u p q γ c π = u p q γ c πstar := by sorry

end StrategicPolicy.MonotoneBinary
