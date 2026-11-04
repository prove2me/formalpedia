-- Prove2me | Theorems.Thm_ThreeSum_LocalCoverBounds_badCount_le_localPrime
-- name    : ThreeSum.LocalCoverBounds.badCount_le_localPrime
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:12:05.022809+00:00
-- url     : https://prove2.me/theorems/8e460ff5-8ed4-4a33-b804-1c6da5967040
-- title:
--   Local Cover Bounds: bad Count le local Prime
-- statement:
--   The Local Cover Bounds construction uses the bad Count le local Prime property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LocalCoverBounds.lean#L313-L317
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LocalCoverBounds.lean#L313-L317

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

theorem ThreeSum.LocalCoverBounds.badCount_le_localPrime {h : ℕ} (hh : 0 < h) :
    2 * degree (512 * h) h + groupSize h ≤ 3 * localPrime h := by sorry
