-- Prove2me | Theorems.Thm_PascalMinusOne_G_dvd_choose
-- name    : PascalMinusOne.G_dvd_choose
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:17:58.985537+00:00
-- url     : https://prove2.me/theorems/4b4806a3-772a-46d9-8a42-67f7972b1977
-- title:
--   Pascal Minus One: G dvd choose
-- statement:
--   The Pascal Minus One construction uses the G dvd choose property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jfairfaxball-348/pascal-minus-one/blob/5f20593464d86ef8c3c34e1c00d84f8a48c0457e/PascalMinusOne/Basic.lean#L32-L34
-- source:
--   https://github.com/jfairfaxball-348/pascal-minus-one/blob/5f20593464d86ef8c3c34e1c00d84f8a48c0457e/PascalMinusOne/Basic.lean#L32-L34

import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Definitions.Def_PascalMinusOne_Basic
set_option autoImplicit true
open PascalMinusOne

theorem PascalMinusOne.G_dvd_choose {N m k : ℕ} (hk : k ∈ admissibleIndices N m) :
    G N m ∣ N.choose k := by sorry
