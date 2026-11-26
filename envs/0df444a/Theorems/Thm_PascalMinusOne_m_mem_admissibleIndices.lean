-- Prove2me | Theorems.Thm_PascalMinusOne_m_mem_admissibleIndices
-- name    : PascalMinusOne.m_mem_admissibleIndices
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:18:45.114724+00:00
-- url     : https://prove2.me/theorems/e60016d6-99bd-4787-9341-04ec8201e96b
-- title:
--   Pascal Minus One: m mem admissible Indices
-- statement:
--   The Pascal Minus One construction uses the m mem admissible Indices property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jfairfaxball-348/pascal-minus-one/blob/5f20593464d86ef8c3c34e1c00d84f8a48c0457e/PascalMinusOne/Basic.lean#L28-L30
-- source:
--   https://github.com/jfairfaxball-348/pascal-minus-one/blob/5f20593464d86ef8c3c34e1c00d84f8a48c0457e/PascalMinusOne/Basic.lean#L28-L30

import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Definitions.Def_PascalMinusOne_Basic
set_option autoImplicit true
open PascalMinusOne

theorem PascalMinusOne.m_mem_admissibleIndices {N m : ℕ} (hm : 0 < m) (hmN : m < N) :
    m ∈ admissibleIndices N m := by sorry
