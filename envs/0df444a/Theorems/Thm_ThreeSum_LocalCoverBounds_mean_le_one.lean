-- Prove2me | Theorems.Thm_ThreeSum_LocalCoverBounds_mean_le_one
-- name    : ThreeSum.LocalCoverBounds.mean_le_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:11:40.913991+00:00
-- url     : https://prove2.me/theorems/6cb9e032-506a-463c-97bd-3590fba3a18f
-- title:
--   Local Cover Bounds: mean le one
-- statement:
--   The Local Cover Bounds construction uses the mean le one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LocalCoverBounds.lean#L132-L139
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LocalCoverBounds.lean#L132-L139

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

theorem ThreeSum.LocalCoverBounds.mean_le_one {L h p : ℕ} (hp : 0 < p)
    (hlo : outputCount L h * 2 ^ (2 * h) ≤ p ^ 2) : mean L h p ≤ 1 := by sorry
