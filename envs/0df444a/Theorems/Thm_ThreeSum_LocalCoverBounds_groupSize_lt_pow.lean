-- Prove2me | Theorems.Thm_ThreeSum_LocalCoverBounds_groupSize_lt_pow
-- name    : ThreeSum.LocalCoverBounds.groupSize_lt_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:11:30.544184+00:00
-- url     : https://prove2.me/theorems/452ca0bd-361b-45ad-adcb-7d394d074a5b
-- title:
--   Local Cover Bounds: group Size lt pow
-- statement:
--   The Local Cover Bounds construction uses the group Size lt pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LocalCoverBounds.lean#L78-L79
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LocalCoverBounds.lean#L78-L79

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

theorem ThreeSum.LocalCoverBounds.groupSize_lt_pow {h : ℕ} (hh : 0 < h) : groupSize h < 2 ^ (2 * h) := by sorry
