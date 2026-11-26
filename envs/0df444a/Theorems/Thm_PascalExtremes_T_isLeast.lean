-- Prove2me | Theorems.Thm_PascalExtremes_T_isLeast
-- name    : PascalExtremes.T_isLeast
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T01:58:53.86621+00:00
-- url     : https://prove2.me/theorems/bbe5c061-82a0-4a7c-b449-818a624c9e1a
-- title:
--   Pascal Extremes: T is Least
-- statement:
--   The Pascal Extremes construction uses the T is Least property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jfairfaxball-348/Pascal-Extremes/blob/a7e414a9e5bcf931c79b2bd4d4ffa81eeb6cfc22/PascalExtremes/TargetAAttainment.lean#L415-L420
-- source:
--   https://github.com/jfairfaxball-348/Pascal-Extremes/blob/a7e414a9e5bcf931c79b2bd4d4ffa81eeb6cfc22/PascalExtremes/TargetAAttainment.lean#L415-L420

module
public import Definitions.Def_PascalExtremes_TargetA
public import Mathlib
public import Definitions.Def_PascalExtremes_TargetAAttainment
set_option autoImplicit true
@[expose] public section
public section
open PascalExtremes

theorem PascalExtremes.T_isLeast
    {p m : ℕ} (hp : p.Prime) (hm2 : 2 ≤ m) (hpm : ¬ p ∣ m) :
    IsLeast (extremalRows p m) (T p m) := by sorry
