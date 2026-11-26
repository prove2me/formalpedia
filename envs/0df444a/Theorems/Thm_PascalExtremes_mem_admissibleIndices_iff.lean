-- Prove2me | Theorems.Thm_PascalExtremes_mem_admissibleIndices_iff
-- name    : PascalExtremes.mem_admissibleIndices_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T01:54:08.094485+00:00
-- url     : https://prove2.me/theorems/4dd4335c-7ad4-4089-b49e-be86135d2bd7
-- title:
--   Pascal Extremes: mem admissible Indices iff
-- statement:
--   The Pascal Extremes construction uses the mem admissible Indices iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jfairfaxball-348/Pascal-Extremes/blob/a7e414a9e5bcf931c79b2bd4d4ffa81eeb6cfc22/PascalExtremes/Basic.lean#L37-L44
-- source:
--   https://github.com/jfairfaxball-348/Pascal-Extremes/blob/a7e414a9e5bcf931c79b2bd4d4ffa81eeb6cfc22/PascalExtremes/Basic.lean#L37-L44

module
public import Mathlib.Algebra.GCDMonoid.Finset
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import Definitions.Def_PascalExtremes_Basic
set_option autoImplicit true
@[expose] public section
public section
open PascalExtremes

theorem PascalExtremes.mem_admissibleIndices_iff {N m k : ℕ} :
    k ∈ admissibleIndices N m ↔ Admissible N m k := by sorry
