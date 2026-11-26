-- Prove2me | Theorems.Thm_PascalExtremes_pow_pred_rP_le
-- name    : PascalExtremes.pow_pred_rP_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T01:55:59.142038+00:00
-- url     : https://prove2.me/theorems/e265848b-11a2-444b-885b-66f771025294
-- title:
--   Pascal Extremes: pow pred r P le
-- statement:
--   The Pascal Extremes construction uses the pow pred r P le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jfairfaxball-348/Pascal-Extremes/blob/a7e414a9e5bcf931c79b2bd4d4ffa81eeb6cfc22/PascalExtremes/Powers.lean#L36-L38
-- source:
--   https://github.com/jfairfaxball-348/Pascal-Extremes/blob/a7e414a9e5bcf931c79b2bd4d4ffa81eeb6cfc22/PascalExtremes/Powers.lean#L36-L38

module
public import Mathlib
public import Definitions.Def_PascalExtremes_Powers
set_option autoImplicit true
@[expose] public section
public section
open PascalExtremes

theorem PascalExtremes.pow_pred_rP_le {p m : ℕ} (hm : m ≠ 0) :
    p ^ (rP p m - 1) ≤ m := by sorry
