-- Prove2me | Theorems.Thm_StrategicPolicy_MonotoneBinary_theorem_3
-- name    : StrategicPolicy.MonotoneBinary.theorem_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T12:59:45.353225+00:00
-- url     : https://prove2.me/theorems/d09edd6d-5854-41b4-b7fd-a9ecb0297dab
-- title:
--   Theorem 3, p. 6 — an outcome monotonic binary policy is optimal
-- statement:
--   Let $\pi^*$ maximize utility over all policies with values in $[0,1]$. If the change cost is outcome monotonic and additive along outcome increasing chains, there is an outcome monotonic binary policy $\pi$ with equal utility:
--
--   $$\pi\in[0,1]^m,\qquad \pi_i<\pi_j\Rightarrow q_i<q_j,\qquad u(\pi,\gamma)=u(\pi^*,\gamma),$$
--
--   where for each $i>1$ with $q_i>\gamma$ the binary rule is
--
--   $$\pi_i=\pi_{i-1}\quad\text{or}\quad\pi_i=\max\{0,\pi_{i-1}-c_{i,i-1}\}.$$
--
--   Thus the structured policy family contains an optimum whenever an optimal policy exists.
--
--   **Formalization Note** The source does not establish that a maximizer exists, so $\pi^*$ and its optimality are hypotheses. The model assumes distinct outcomes, free staying, and the paper's standing positive cost condition. Policy monotonicity means the implication compatible with (9), and additivity concerns strictly improving outcome chains. The $i-1$ relation is represented without truncated subtraction in Lean.
-- source:
--   Tsirtsis et al., Optimal Decision Making Under Strategic Behavior, arXiv:1905.09239v5, p. 6, Theorem 3; proof p. 18, Appendix A.3

import Mathlib
import Definitions.Def_StrategicPolicy_MonotoneBinary_Setting

namespace StrategicPolicy.MonotoneBinary

variable {m : ℕ}

theorem theorem_3 [NeZero m]
    (p q : Fin m → ℝ) (γ : ℝ) (c : Fin m → Fin m → ℝ)
    (hstanding : Standing p q γ c) (hcost : OMCost q c)
    (hadd : AdditiveCost q c)
    (πstar : Fin m → ℝ) (hopt : Optimal p q γ c πstar) :
    ∃ π ∈ Policies m, OMBinary q γ c π ∧ u p q γ c π = u p q γ c πstar := by sorry

end StrategicPolicy.MonotoneBinary
