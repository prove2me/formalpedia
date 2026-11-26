-- Prove2me | Theorems.Thm_PascalMinusOne_mem_admissibleIndices_iff
-- name    : PascalMinusOne.mem_admissibleIndices_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:17:06.241893+00:00
-- url     : https://prove2.me/theorems/aa765e0c-ce40-5729-8a3c-ece516bcd7a8
-- title:
--   Pascal Minus One: mem admissible Indices iff
-- statement:
--   The Pascal Minus One construction uses the mem admissible Indices iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jfairfaxball-348/pascal-minus-one/blob/5f20593464d86ef8c3c34e1c00d84f8a48c0457e/PascalMinusOne/Basic.lean#L19-L26
-- source:
--   https://github.com/jfairfaxball-348/pascal-minus-one/blob/5f20593464d86ef8c3c34e1c00d84f8a48c0457e/PascalMinusOne/Basic.lean#L19-L26

import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Definitions.Def_PascalMinusOne_Basic
set_option autoImplicit true
open PascalMinusOne

theorem PascalMinusOne.mem_admissibleIndices_iff {N m k : ℕ} :
    k ∈ admissibleIndices N m ↔ Admissible N m k := by sorry
