-- Prove2me | Theorems.Thm_RamanujanNotebooks_entry_33_2_4
-- name    : RamanujanNotebooks.entry_33_2_4
-- status  : Open
-- author  : @Xiang Huang
-- created : 2026-10-07T07:37:31.630131+00:00
-- url     : https://prove2.me/theorems/6f679a68-983f-4d70-a3d9-1c975a19ade4
-- title:
--   Ramanujan's cubic transformation of the hypergeometric function with parameters 1/3, 2/3; 1
-- statement:
--   There is $\delta>0$ such that for all real $x$ with $|x|<\delta$, ${}_2F_1\!\big(\tfrac13,\tfrac23;1;1-\big(\tfrac{1-x}{1+2x}\big)^3\big)=(1+2x)\,{}_2F_1\!\big(\tfrac13,\tfrac23;1;x^3\big)$.
-- source:
--   Bruce C. Berndt, Ramanujan's Notebooks, Part V (Springer, 1998), Chapter 33, Corollary 2.4, p. 97, eq. (2.23).

import Mathlib
import Definitions.Def_RamanujanNotebooks_shared_hyp2F1R
import Definitions.Def_RamanujanNotebooks_shared_shiftedFactorialR

namespace RamanujanNotebooks
theorem entry_33_2_4 :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x : ℝ, |x| < δ →
      hyp2F1R (1 / 3) (2 / 3) 1 (1 - ((1 - x) / (1 + 2 * x)) ^ 3) = (1 + 2 * x) * hyp2F1R (1 / 3) (2 / 3) 1 (x ^ 3) := by sorry
end RamanujanNotebooks
