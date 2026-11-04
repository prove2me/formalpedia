-- Prove2me | Theorems.Thm_ThreeSum_LocalCoverBounds_groupSize_le_pow
-- name    : ThreeSum.LocalCoverBounds.groupSize_le_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:11:41.242628+00:00
-- url     : https://prove2.me/theorems/de0b1908-368a-45cf-b21c-ca47b434cffa
-- title:
--   Local Cover Bounds: group Size le pow
-- statement:
--   The Local Cover Bounds construction uses the group Size le pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LocalCoverBounds.lean#L81-L82
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LocalCoverBounds.lean#L81-L82

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

theorem ThreeSum.LocalCoverBounds.groupSize_le_pow (h : ℕ) : groupSize h ≤ 2 ^ (2 * h) := by sorry
