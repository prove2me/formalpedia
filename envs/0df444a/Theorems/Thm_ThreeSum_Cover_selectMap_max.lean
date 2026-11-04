-- Prove2me | Theorems.Thm_ThreeSum_Cover_selectMap_max
-- name    : ThreeSum.Cover.selectMap_max
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:07:27.804556+00:00
-- url     : https://prove2.me/theorems/1d0c717a-3390-4092-9700-2b9303df9ec5
-- title:
--   Cover: select Map max
-- statement:
--   The Cover construction uses the select Map max property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Greedy.lean#L32-L42
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Greedy.lean#L32-L42

import Definitions.Def_Submission_ThreeSum_Cover
import Mathlib.Data.List.MinMax
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Tactic.Ring
import Aesop
import Definitions.Def_Submission_ThreeSum_Greedy
set_option autoImplicit false
open ThreeSum ThreeSum.Cover
open Finset
open scoped BigOperators
variable {Ω U : Type*} [Inhabited Ω] [DecidableEq U]

theorem ThreeSum.Cover.selectMap_max (maps : List Ω) (covers : Ω → U → Prop)
    [DecidableRel covers] (targets : Finset U) {ω : Ω} (hω : ω ∈ maps) :
    (targets.filter (covers ω)).card ≤
      (targets.filter (covers (selectMap maps covers targets))).card := by sorry
