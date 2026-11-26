-- Prove2me | Theorems.Thm_PascalExtremes_lt_pow_rP
-- name    : PascalExtremes.lt_pow_rP
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T01:55:40.856074+00:00
-- url     : https://prove2.me/theorems/f5816ddd-a331-5da9-bc3b-21c9e500cfd8
-- title:
--   Pascal Extremes: lt pow r P
-- statement:
--   The Pascal Extremes construction uses the lt pow r P property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jfairfaxball-348/Pascal-Extremes/blob/a7e414a9e5bcf931c79b2bd4d4ffa81eeb6cfc22/PascalExtremes/Powers.lean#L18-L20
-- source:
--   https://github.com/jfairfaxball-348/Pascal-Extremes/blob/a7e414a9e5bcf931c79b2bd4d4ffa81eeb6cfc22/PascalExtremes/Powers.lean#L18-L20

module
public import Mathlib
public import Definitions.Def_PascalExtremes_Powers
set_option autoImplicit true
@[expose] public section
public section
open PascalExtremes

theorem PascalExtremes.lt_pow_rP {p m : ℕ} (hp : 1 < p) :
    m < p ^ rP p m := by sorry
