-- Prove2me | Theorems.Thm_PascalMinusOne_dvd_iff_signedZeroSum_digitSums
-- name    : PascalMinusOne.dvd_iff_signedZeroSum_digitSums
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:18:17.849719+00:00
-- url     : https://prove2.me/theorems/b25a35d7-3aaf-451d-9688-295a11c721b0
-- title:
--   Pascal Minus One: dvd iff signed Zero Sum digit Sums
-- statement:
--   Divisibility by `m` is the signed zero-sum condition on the even/odd base-`p`
--   digit totals when `p ≡ -1 (mod m)`.
--
--   Source: https://github.com/jfairfaxball-348/pascal-minus-one/blob/5f20593464d86ef8c3c34e1c00d84f8a48c0457e/PascalMinusOne/MinusOne.lean#L66-L81
-- source:
--   https://github.com/jfairfaxball-348/pascal-minus-one/blob/5f20593464d86ef8c3c34e1c00d84f8a48c0457e/PascalMinusOne/MinusOne.lean#L66-L81

import Definitions.Def_PascalMinusOne_Basic
import Definitions.Def_PascalMinusOne_Digits
import Definitions.Def_PascalMinusOne_Kummer
import Definitions.Def_PascalMinusOne_SignedTokens
import Mathlib.Data.Nat.Digits.Div
import Mathlib.Data.List.GetD
import Definitions.Def_PascalMinusOne_MinusOne
set_option autoImplicit true
open PascalMinusOne

theorem PascalMinusOne.dvd_iff_signedZeroSum_digitSums {m p k : ℕ}
    (hm : 2 ≤ m) (hpm : p % m = m - 1) :
    m ∣ k ↔ SignedZeroSum m (evenDigitSum p k) (oddDigitSum p k) := by sorry
