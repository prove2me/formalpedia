-- Prove2me | Theorems.Thm_PascalExtremes_m_mem_admissibleIndices
-- name    : PascalExtremes.m_mem_admissibleIndices
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T01:54:19.173922+00:00
-- url     : https://prove2.me/theorems/ae629010-2cab-5658-8415-daef81793546
-- title:
--   Pascal Extremes: m mem admissible Indices
-- statement:
--   The Pascal Extremes construction uses the m mem admissible Indices property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jfairfaxball-348/Pascal-Extremes/blob/a7e414a9e5bcf931c79b2bd4d4ffa81eeb6cfc22/PascalExtremes/Basic.lean#L46-L48
-- source:
--   https://github.com/jfairfaxball-348/Pascal-Extremes/blob/a7e414a9e5bcf931c79b2bd4d4ffa81eeb6cfc22/PascalExtremes/Basic.lean#L46-L48

module
public import Mathlib.Algebra.GCDMonoid.Finset
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import Definitions.Def_PascalExtremes_Basic
set_option autoImplicit true
@[expose] public section
public section
open PascalExtremes

theorem PascalExtremes.m_mem_admissibleIndices {N m : ℕ} (hm : 0 < m) (hmN : m < N) :
    m ∈ admissibleIndices N m := by sorry
