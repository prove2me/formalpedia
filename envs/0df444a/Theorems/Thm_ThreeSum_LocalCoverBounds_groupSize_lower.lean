-- Prove2me | Theorems.Thm_ThreeSum_LocalCoverBounds_groupSize_lower
-- name    : ThreeSum.LocalCoverBounds.groupSize_lower
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:11:34.545194+00:00
-- url     : https://prove2.me/theorems/4253d6d8-d671-4730-a457-334e7fcc4f42
-- title:
--   Local Cover Bounds: group Size lower
-- statement:
--   The Local Cover Bounds construction uses the group Size lower property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LocalCoverBounds.lean#L84-L87
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LocalCoverBounds.lean#L84-L87

import Definitions.Def_Submission_ThreeSum_LayerCounts
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Nat.Sqrt
import Mathlib.NumberTheory.Bertrand
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Definitions.Def_Submission_ThreeSum_LocalCoverBounds
set_option autoImplicit false
open ThreeSum ThreeSum.LocalCoverBounds
open scoped BigOperators

theorem ThreeSum.LocalCoverBounds.groupSize_lower (h : ℕ) :
    2 ^ (2 * h) ≤ (2 * h + 1) * groupSize h := by sorry
