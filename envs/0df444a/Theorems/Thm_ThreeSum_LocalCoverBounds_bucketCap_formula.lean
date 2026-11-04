-- Prove2me | Theorems.Thm_ThreeSum_LocalCoverBounds_bucketCap_formula
-- name    : ThreeSum.LocalCoverBounds.bucketCap_formula
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:11:51.486569+00:00
-- url     : https://prove2.me/theorems/52e4478f-04d4-48df-a3b3-4212f540d70c
-- title:
--   Local Cover Bounds: bucket Cap formula
-- statement:
--   The Local Cover Bounds construction uses the bucket Cap formula property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LocalCoverBounds.lean#L244-L245
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LocalCoverBounds.lean#L244-L245

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

theorem ThreeSum.LocalCoverBounds.bucketCap_formula (V p : ℕ) :
    bucketCap V p = (4 * (p + V) + p - 1) / p := by sorry
