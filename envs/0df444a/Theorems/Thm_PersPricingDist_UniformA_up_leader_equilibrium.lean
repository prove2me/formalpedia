-- Prove2me | Theorems.Thm_PersPricingDist_UniformA_up_leader_equilibrium
-- name    : PersPricingDist.UniformA.up_leader_equilibrium
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T02:45:11.292076+00:00
-- url     : https://prove2.me/theorems/17e8a619-1700-4559-937e-2d9a3b27eaea
-- title:
--   OA p. 3 — A’s optimal leader price with personalized B
-- statement:
--   When A charges a uniform price and B responds with personalized prices, set $w^*_{UP}=s(1+v)/[2(1+s)]$. Then A's unique globally optimal leader price is
--
--   $$p_A(w^*_{UP})=w^*_{UP}+\frac{1-v}{2}.$$
--
--   The leader maximizes retail receipts plus wholesale receipts from B's sales over all real uniform prices. **Formalization Note** B's selected consumer-by-consumer continuation is the response specified in the Setting; the theorem asserts A's global optimum, beyond the interior first-order calculation.
-- source:
--   Jullien, Reisinger & Rey, Personalized Pricing and Distribution Strategies, authors' manuscript of March 2022 (Management Science, doi:10.1287/mnsc.2022.4437; PDF sha256 25a6c84ac0c48c6720f6a9e1f9b1f1ec516412c31dac044ac84c1d4c72dfc253), OA p. 3 (PDF 36)

import Mathlib
import Definitions.Def_PersPricingDist_UniformA_Setting

namespace PersPricingDist.UniformA

/-- A's globally optimal uniform price in the UP continuation at the
wholesale price of Online Appendix A, p. 3. -/
theorem up_leader_equilibrium (M : Model) (hM : M.Standing) :
    M.IsLeaderOptUP M.wUP (M.pA_UP M.wUP) ∧
    (∀ pA : ℝ, M.IsLeaderOptUP M.wUP pA → pA = M.pA_UP M.wUP) := by sorry
end PersPricingDist.UniformA
