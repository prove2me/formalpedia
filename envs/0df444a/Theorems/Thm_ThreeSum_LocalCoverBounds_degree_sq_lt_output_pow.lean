-- Prove2me | Theorems.Thm_ThreeSum_LocalCoverBounds_degree_sq_lt_output_pow
-- name    : ThreeSum.LocalCoverBounds.degree_sq_lt_output_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:11:41.387662+00:00
-- url     : https://prove2.me/theorems/3b56a43e-8ea4-4e59-9f71-ebe6e8821623
-- title:
--   Local Cover Bounds: degree sq lt output pow
-- statement:
--   Exact strict version of the degree-square estimate needed to compare the
--   degree with the selected prime.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LocalCoverBounds.lean#L91-L100
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LocalCoverBounds.lean#L91-L100

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

theorem ThreeSum.LocalCoverBounds.degree_sq_lt_output_pow {L h : ℕ} (hh : 0 < h) (hL : 2 * h ≤ L) :
    degree L h ^ 2 < outputCount L h * 2 ^ (2 * h) := by sorry
