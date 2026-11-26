-- Prove2me | Theorems.Thm_PascalMinusOne_plus_one_valuation
-- name    : PascalMinusOne.plus_one_valuation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:18:11.354703+00:00
-- url     : https://prove2.me/theorems/3d9f3415-cd63-52b1-8887-b57192ab7d55
-- title:
--   Pascal Minus One: plus one valuation
-- statement:
--   The `p ≡ 1 (mod m)` valuation theorem for the restricted binomial gcd.
--
--   For `m ∣ N` and `m < N`, the valuation is one exactly when the base-`p`
--   digit sum of `N` is the minimal positive multiple `m`; otherwise it is zero.
--   The statement includes `m = 1`, which is useful after scaling small moduli.
--
--   Source: https://github.com/jfairfaxball-348/pascal-minus-one/blob/5f20593464d86ef8c3c34e1c00d84f8a48c0457e/PascalMinusOne/PlusOne.lean#L340-L413
-- source:
--   https://github.com/jfairfaxball-348/pascal-minus-one/blob/5f20593464d86ef8c3c34e1c00d84f8a48c0457e/PascalMinusOne/PlusOne.lean#L340-L413

import Definitions.Def_PascalMinusOne_MinusOne
import Mathlib.Data.Nat.Digits.Lemmas
import Definitions.Def_PascalMinusOne_PlusOne
set_option autoImplicit true
open PascalMinusOne

theorem PascalMinusOne.plus_one_valuation
    {m p N : ℕ} (hm : 0 < m) (hp : p.Prime)
    (hpm : p % m = 1 % m) (hmN : m ∣ N) (hNm : m < N) :
    padicValNat p (G N m) = plusOneExpectedValuation m p N := by sorry
