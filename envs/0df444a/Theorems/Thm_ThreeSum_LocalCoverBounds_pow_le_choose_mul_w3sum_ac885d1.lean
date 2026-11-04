-- Prove2me | Theorems.Thm_ThreeSum_LocalCoverBounds_pow_le_choose_mul_w3sum_ac885d1
-- name    : ThreeSum.LocalCoverBounds.pow_le_choose_mul_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:11:30.091083+00:00
-- url     : https://prove2.me/theorems/35737511-165a-4395-ad2f-350d7b882d17
-- title:
--   Local Cover Bounds: pow le choose mul
-- statement:
--   Choose one coordinate from each of `r` disjoint blocks of size `c`. This
--   is a direct finite injection giving an exact binomial lower bound.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LocalCoverBounds.lean#L36-L62
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LocalCoverBounds.lean#L36-L62

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

theorem ThreeSum.LocalCoverBounds.pow_le_choose_mul_w3sum_ac885d1 (c r : ℕ) : c ^ r ≤ (c * r).choose r := by sorry
