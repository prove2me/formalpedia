-- Prove2me | Theorems.Thm_ThreeSum_LocalCoverBounds_localPrime_sq_lower
-- name    : ThreeSum.LocalCoverBounds.localPrime_sq_lower
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:12:01.19606+00:00
-- url     : https://prove2.me/theorems/433297e3-73e4-49cf-b4f5-e42025f7dbc7
-- title:
--   Local Cover Bounds: local Prime sq lower
-- statement:
--   The Local Cover Bounds construction uses the local Prime sq lower property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LocalCoverBounds.lean#L294-L296
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LocalCoverBounds.lean#L294-L296

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

theorem ThreeSum.LocalCoverBounds.localPrime_sq_lower (h : ℕ) :
    outputCount (512 * h) h * 2 ^ (2 * h) ≤ localPrime h ^ 2 := by sorry
