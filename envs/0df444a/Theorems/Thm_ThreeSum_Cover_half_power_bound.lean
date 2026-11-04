-- Prove2me | Theorems.Thm_ThreeSum_Cover_half_power_bound
-- name    : ThreeSum.Cover.half_power_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:07:37.849572+00:00
-- url     : https://prove2.me/theorems/016815fc-130a-447a-8c2d-e9848e345d26
-- title:
--   Cover: half power bound
-- statement:
--   Each block of a iterations shrinks the geometric upper bound by 1/2.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Greedy.lean#L118-L128
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Greedy.lean#L118-L128

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

theorem ThreeSum.Cover.half_power_bound (a : ℕ) (ha : 0 < a) : 2 * (a - 1) ^ a ≤ a ^ a := by sorry
