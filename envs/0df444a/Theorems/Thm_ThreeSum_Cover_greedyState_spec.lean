-- Prove2me | Theorems.Thm_ThreeSum_Cover_greedyState_spec
-- name    : ThreeSum.Cover.greedyState_spec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:07:35.798195+00:00
-- url     : https://prove2.me/theorems/512e43a3-1b20-4d9a-9516-0835786a89cd
-- title:
--   Cover: greedy State spec
-- statement:
--   The Cover construction uses the greedy State spec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Greedy.lean#L64-L72
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Greedy.lean#L64-L72

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

theorem ThreeSum.Cover.greedyState_spec (maps : List Ω) (covers : Ω → U → Prop)
    [DecidableRel covers] (targets : Finset U) (t : ℕ) (u : U) :
    u ∈ greedyState maps covers targets t ↔
      u ∈ targets ∧ ∀ ω ∈ greedyChoices maps covers targets t, ¬ covers ω u := by sorry
