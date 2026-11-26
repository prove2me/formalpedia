-- Prove2me | Theorems.Thm_PascalExtremes_rP_pow_add_one
-- name    : PascalExtremes.rP_pow_add_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T01:56:01.245653+00:00
-- url     : https://prove2.me/theorems/0f149c67-8d60-40b3-91e4-68b4eb12ae0a
-- title:
--   Pascal Extremes: r P pow add one
-- statement:
--   The Pascal Extremes construction uses the r P pow add one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jfairfaxball-348/Pascal-Extremes/blob/a7e414a9e5bcf931c79b2bd4d4ffa81eeb6cfc22/PascalExtremes/Powers.lean#L40-L55
-- source:
--   https://github.com/jfairfaxball-348/Pascal-Extremes/blob/a7e414a9e5bcf931c79b2bd4d4ffa81eeb6cfc22/PascalExtremes/Powers.lean#L40-L55

module
public import Mathlib
public import Definitions.Def_PascalExtremes_Powers
set_option autoImplicit true
@[expose] public section
public section
open PascalExtremes

theorem PascalExtremes.rP_pow_add_one {p a : ℕ} (hp : 1 < p) (ha : 1 ≤ a) :
    rP p (p ^ a + 1) = a + 1 := by sorry
