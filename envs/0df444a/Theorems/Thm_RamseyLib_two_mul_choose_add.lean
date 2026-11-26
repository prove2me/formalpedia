-- Prove2me | Theorems.Thm_RamseyLib_two_mul_choose_add
-- name    : RamseyLib.two_mul_choose_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:15:48.04986+00:00
-- url     : https://prove2.me/theorems/4ca61eca-76fb-55a2-ad2f-d2c4fc0cd908
-- title:
--   Ramsey Lib: two mul choose add
-- statement:
--   The Ramsey Lib construction uses the two mul choose add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/ramsey-graph-bounds/blob/562986a7ce9edf086c20b3a2b8c7d5ace2ffd843/RamseyLib/Bounds.lean#L131-L134
-- source:
--   https://github.com/jtraverso/ramsey-graph-bounds/blob/562986a7ce9edf086c20b3a2b8c7d5ace2ffd843/RamseyLib/Bounds.lean#L131-L134

module
public import Mathlib
public import Definitions.Def_RamseyLib_Bounds
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open RamseyLib

theorem RamseyLib.two_mul_choose_add (k : ℕ) : 2 * k.choose 2 + k = k ^ 2 := by sorry
