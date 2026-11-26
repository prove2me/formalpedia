-- Prove2me | Theorems.Thm_PascalMinusOnePalomar_minus_one_valuation
-- name    : PascalMinusOnePalomar.minus_one_valuation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:27:17.695003+00:00
-- url     : https://prove2.me/theorems/14e75f26-07cb-4e77-9f12-d96ad8204842
-- title:
--   Pascal Minus One Palomar: minus one valuation
-- statement:
--   The Pascal Minus One Palomar construction uses the minus one valuation property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jfairfaxball-348/pascal-minus-one/blob/5f20593464d86ef8c3c34e1c00d84f8a48c0457e/Solution.lean#L60-L69
-- source:
--   https://github.com/jfairfaxball-348/pascal-minus-one/blob/5f20593464d86ef8c3c34e1c00d84f8a48c0457e/Solution.lean#L60-L69

import Definitions.Def_PascalMinusOne
import Definitions.Def_PascalMinusOne_Solution
import Theorems.Thm_PascalMinusOne_minus_one_valuation

set_option autoImplicit true
open PascalMinusOnePalomar

theorem PascalMinusOnePalomar.minus_one_valuation
    {m N p : ℕ}
    (hm : 3 ≤ m) (hmN : m ∣ N) (hNm : m < N)
    (hp : p.Prime) (hpm : p % m = m - 1) :
    padicValNat p (G N m) =
      minusOneExpectedValuation m p (evenDigitSum p N) (oddDigitSum p N) := by sorry
