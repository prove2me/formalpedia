-- Prove2me | Theorems.Thm_PascalMinusOne_mixed_case_one_borrow_of_gt
-- name    : PascalMinusOne.mixed_case_one_borrow_of_gt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:19:43.42453+00:00
-- url     : https://prove2.me/theorems/8feb23ab-b2af-5801-9763-d569b900895d
-- title:
--   Pascal Minus One: mixed case one borrow of gt
-- statement:
--   In the mixed token case with `p > m`, the witness `m * p^(t-1)` creates
--   exactly one carry at the leading boundary.
--
--   Source: https://github.com/jfairfaxball-348/pascal-minus-one/blob/5f20593464d86ef8c3c34e1c00d84f8a48c0457e/PascalMinusOne/MinusOne.lean#L957-L1097
-- source:
--   https://github.com/jfairfaxball-348/pascal-minus-one/blob/5f20593464d86ef8c3c34e1c00d84f8a48c0457e/PascalMinusOne/MinusOne.lean#L957-L1097

import Definitions.Def_PascalMinusOne_Basic
import Definitions.Def_PascalMinusOne_Digits
import Definitions.Def_PascalMinusOne_Kummer
import Definitions.Def_PascalMinusOne_SignedTokens
import Mathlib.Data.Nat.Digits.Div
import Mathlib.Data.List.GetD
import Definitions.Def_PascalMinusOne_MinusOne
set_option autoImplicit true
open PascalMinusOne

theorem PascalMinusOne.mixed_case_one_borrow_of_gt
    {m p N : ℕ} (hm : 3 ≤ m) (hp : p.Prime) (hpm : p % m = m - 1)
    (hpmgt : m < p)
    (hmixed : evenDigitSum p N = 1 ∧ oddDigitSum p N = 1) :
    ∃ k, Admissible N m k ∧ padicValNat p (N.choose k) = 1 := by sorry
