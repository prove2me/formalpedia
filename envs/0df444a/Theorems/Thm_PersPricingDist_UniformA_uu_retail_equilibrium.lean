-- Prove2me | Theorems.Thm_PersPricingDist_UniformA_uu_retail_equilibrium
-- name    : PersPricingDist.UniformA.uu_retail_equilibrium
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T02:45:05.586551+00:00
-- url     : https://prove2.me/theorems/94c50995-98ed-4e7a-8d50-016449e10352
-- title:
--   OA pp. 1–2 — UU equilibrium retail prices
-- statement:
--   When A and B both charge uniform retail prices, set the wholesale price to $w^*_{UU}=s[4(1+v)+s]/[2(4+5s)]$. The retail price pair
--
--   $$p_A(w)=\frac{2-s+3w-v}{4-s},\qquad p_B(w)=\frac{v(2-s)+w(2+s)-s}{4-s}$$
--
--   at $w=w^*_{UU}$ is the unique downstream Nash equilibrium: each price maximizes that firm's total variable profit against the other's price, among all real prices. This connects the paper's interior calculations to the full retail game. **Formalization Note** The claim is global best response and uniqueness at the stated wholesale price; it does not infer a global reaction function merely from the first-order conditions on the interior demand region.
-- source:
--   Jullien, Reisinger & Rey, Personalized Pricing and Distribution Strategies, authors' manuscript of March 2022 (Management Science, doi:10.1287/mnsc.2022.4437; PDF sha256 25a6c84ac0c48c6720f6a9e1f9b1f1ec516412c31dac044ac84c1d4c72dfc253), OA pp. 1–2 (PDF 34–35)

import Mathlib
import Definitions.Def_PersPricingDist_UniformA_Setting

namespace PersPricingDist.UniformA

/-- The downstream UU equilibrium prices of Online Appendix A, pp. 1–2,
at the wholesale price selected on OA p. 2. -/
theorem uu_retail_equilibrium (M : Model) (hM : M.Standing) :
    M.IsNashUU M.wUU (M.pA_UU M.wUU) (M.pB_UU M.wUU) ∧
    (∀ pA pB : ℝ, M.IsNashUU M.wUU pA pB →
      pA = M.pA_UU M.wUU ∧ pB = M.pB_UU M.wUU) := by sorry
end PersPricingDist.UniformA
