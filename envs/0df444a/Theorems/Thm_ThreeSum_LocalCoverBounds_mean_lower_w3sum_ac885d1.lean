-- Prove2me | Theorems.Thm_ThreeSum_LocalCoverBounds_mean_lower_w3sum_ac885d1
-- name    : ThreeSum.LocalCoverBounds.mean_lower_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:11:41.459211+00:00
-- url     : https://prove2.me/theorems/bad9b6b7-f3f1-48cb-be55-3ec321ba0b4c
-- title:
--   Local Cover Bounds: mean lower
-- statement:
--   The factor 16 permits a prime above the rounded square-root threshold.
--   Together with the central-binomial estimate it gives the stated explicit
--   lower bound on the probability scale.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LocalCoverBounds.lean#L144-L157
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LocalCoverBounds.lean#L144-L157

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

theorem ThreeSum.LocalCoverBounds.mean_lower_w3sum_ac885d1 {L h p : ℕ} (hL : 2 * h ≤ L) (hp : 0 < p)
    (hup : p ^ 2 ≤ 16 * (outputCount L h * 2 ^ (2 * h))) :
    1 / (16 * (2 * (h : ℝ) + 1)) ≤ mean L h p := by sorry
