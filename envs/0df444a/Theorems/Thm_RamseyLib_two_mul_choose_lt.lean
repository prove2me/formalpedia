-- Prove2me | Theorems.Thm_RamseyLib_two_mul_choose_lt
-- name    : RamseyLib.two_mul_choose_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:15:49.880638+00:00
-- url     : https://prove2.me/theorems/8b0e3686-eec8-4234-a42a-25952900a9d5
-- title:
--   Ramsey Lib: two mul choose lt
-- statement:
--   The Ramsey Lib construction uses the two mul choose lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/ramsey-graph-bounds/blob/562986a7ce9edf086c20b3a2b8c7d5ace2ffd843/RamseyLib/Bounds.lean#L144-L161
-- source:
--   https://github.com/jtraverso/ramsey-graph-bounds/blob/562986a7ce9edf086c20b3a2b8c7d5ace2ffd843/RamseyLib/Bounds.lean#L144-L161

module
public import Mathlib
public import Definitions.Def_RamseyLib_Bounds
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open RamseyLib

theorem RamseyLib.two_mul_choose_lt (k n : ℕ) (hk : 3 ≤ k) (hn : n ^ 2 ≤ 2 ^ k) :
    2 * n.choose k < 2 ^ (k.choose 2) := by sorry
