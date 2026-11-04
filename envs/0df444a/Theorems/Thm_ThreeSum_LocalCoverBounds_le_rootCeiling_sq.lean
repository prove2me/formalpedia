-- Prove2me | Theorems.Thm_ThreeSum_LocalCoverBounds_le_rootCeiling_sq
-- name    : ThreeSum.LocalCoverBounds.le_rootCeiling_sq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:11:41.736403+00:00
-- url     : https://prove2.me/theorems/114c3677-8ec5-495d-9482-2c4203cdfe15
-- title:
--   Local Cover Bounds: le root Ceiling sq
-- statement:
--   The Local Cover Bounds construction uses the le root Ceiling sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LocalCoverBounds.lean#L168-L172
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LocalCoverBounds.lean#L168-L172

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

theorem ThreeSum.LocalCoverBounds.le_rootCeiling_sq (N : ℕ) : N ≤ rootCeiling N ^ 2 := by sorry
