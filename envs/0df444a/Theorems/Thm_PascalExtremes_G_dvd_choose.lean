-- Prove2me | Theorems.Thm_PascalExtremes_G_dvd_choose
-- name    : PascalExtremes.G_dvd_choose
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T01:54:14.01725+00:00
-- url     : https://prove2.me/theorems/05042493-2a13-4cdb-810b-d0a81eaa121a
-- title:
--   Pascal Extremes: G dvd choose
-- statement:
--   The Pascal Extremes construction uses the G dvd choose property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jfairfaxball-348/Pascal-Extremes/blob/a7e414a9e5bcf931c79b2bd4d4ffa81eeb6cfc22/PascalExtremes/Basic.lean#L50-L52
-- source:
--   https://github.com/jfairfaxball-348/Pascal-Extremes/blob/a7e414a9e5bcf931c79b2bd4d4ffa81eeb6cfc22/PascalExtremes/Basic.lean#L50-L52

module
public import Mathlib.Algebra.GCDMonoid.Finset
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import Definitions.Def_PascalExtremes_Basic
set_option autoImplicit true
@[expose] public section
public section
open PascalExtremes

theorem PascalExtremes.G_dvd_choose {N m k : ℕ} (hk : k ∈ admissibleIndices N m) :
    G N m ∣ N.choose k := by sorry
