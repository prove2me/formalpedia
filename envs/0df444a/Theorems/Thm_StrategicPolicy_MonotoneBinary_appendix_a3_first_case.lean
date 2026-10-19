-- Prove2me | Theorems.Thm_StrategicPolicy_MonotoneBinary_appendix_a3_first_case
-- name    : StrategicPolicy.MonotoneBinary.appendix_a3_first_case
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T12:59:42.437101+00:00
-- url     : https://prove2.me/theorems/1493b6b5-ce7f-453e-aba5-783415241885
-- title:
--   Appendix A.3, p. 18 — raising a policy value to its predecessor
-- statement:
--   Let $\pi^*$ be an optimal outcome monotonic policy under an additive, outcome monotonic cost. Choose an index $i>1$ with $q_i>\gamma$ that is the highest-outcome index violating the binary rule (9); write $j=i-1$. Suppose
--
--   $$\pi^*_j-c_{ij}<\pi^*_i<\pi^*_j.$$
--
--   Define $\pi'$ by replacing only $\pi^*_i$ with $\pi^*_j$. Then
--
--   $$u(\pi^*,\gamma)\le u(\pi',\gamma).$$
--
--   This is the first improvement case used in Appendix A.3 to reach a binary policy.
--
--   **Formalization Note** The first relevant violator condition is stated as no lower Lean index violating either case of (9) above $\gamma$. The paper's setup chooses the highest-outcome violator; restricting to $q_i>\gamma$ follows (9). The standing model assumes distinct outcomes and the disclosed readings of (1) and additivity. The theorem asserts the utility comparison; the updated policy is the paper's $\pi'$.
-- source:
--   Tsirtsis et al., Optimal Decision Making Under Strategic Behavior, arXiv:1905.09239v5, p. 18, Appendix A.3, first case after the setup of the highest-outcome violator

import Mathlib
import Definitions.Def_StrategicPolicy_MonotoneBinary_Setting

namespace StrategicPolicy.MonotoneBinary

variable {m : ℕ}

theorem appendix_a3_first_case [NeZero m]
    (p q : Fin m → ℝ) (γ : ℝ) (c : Fin m → Fin m → ℝ)
    (hstanding : Standing p q γ c) (hcost : OMCost q c)
    (hadd : AdditiveCost q c)
    (πstar : Fin m → ℝ) (hopt : Optimal p q γ c πstar)
    (hmono : OMPolicy q πstar)
    (i j : Fin m) (hprev : j.val + 1 = i.val) (hgain : γ < q i)
    (hhighest : HighestViolator γ c q πstar i)
    (hcase : πstar j - c i j < πstar i ∧ πstar i < πstar j) :
    u p q γ c πstar ≤ u p q γ c (Function.update πstar i (πstar j)) := by sorry

end StrategicPolicy.MonotoneBinary
