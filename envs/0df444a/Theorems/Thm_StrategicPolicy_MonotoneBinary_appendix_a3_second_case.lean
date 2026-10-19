-- Prove2me | Theorems.Thm_StrategicPolicy_MonotoneBinary_appendix_a3_second_case
-- name    : StrategicPolicy.MonotoneBinary.appendix_a3_second_case
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T12:59:43.530523+00:00
-- url     : https://prove2.me/theorems/f4c3b01f-9259-4fb9-b364-23cd87b7df93
-- title:
--   Appendix A.3, p. 18 — raising a policy value to the cost threshold
-- statement:
--   Let $\pi^*$ be an optimal outcome monotonic policy under an additive, outcome monotonic cost. Choose an index $i>1$ with $q_i>\gamma$ that is the highest-outcome index violating the binary rule (9); write $j=i-1$. Suppose
--
--   $$\pi^*_i<\pi^*_j-c_{ij}.$$
--
--   Define $\pi'$ by replacing only $\pi^*_i$ with $\pi^*_j-c_{ij}$. Then
--
--   $$u(\pi^*,\gamma)\le u(\pi',\gamma).$$
--
--   This is the second improvement case used in Appendix A.3 to reach a binary policy.
--
--   **Formalization Note** The first relevant violator condition excludes earlier violations of either case of (9) above $\gamma$. The restriction $q_i>\gamma$ follows the domain of (9). The standing model assumes distinct outcomes and the disclosed readings of (1) and additivity.
-- source:
--   Tsirtsis et al., Optimal Decision Making Under Strategic Behavior, arXiv:1905.09239v5, p. 18, Appendix A.3, second case after the setup of the highest-outcome violator

import Mathlib
import Definitions.Def_StrategicPolicy_MonotoneBinary_Setting

namespace StrategicPolicy.MonotoneBinary

variable {m : ℕ}

theorem appendix_a3_second_case [NeZero m]
    (p q : Fin m → ℝ) (γ : ℝ) (c : Fin m → Fin m → ℝ)
    (hstanding : Standing p q γ c) (hcost : OMCost q c)
    (hadd : AdditiveCost q c)
    (πstar : Fin m → ℝ) (hopt : Optimal p q γ c πstar)
    (hmono : OMPolicy q πstar)
    (i j : Fin m) (hprev : j.val + 1 = i.val) (hgain : γ < q i)
    (hhighest : HighestViolator γ c q πstar i)
    (hcase : πstar i < πstar j - c i j) :
    u p q γ c πstar ≤
      u p q γ c (Function.update πstar i (πstar j - c i j)) := by sorry

end StrategicPolicy.MonotoneBinary
