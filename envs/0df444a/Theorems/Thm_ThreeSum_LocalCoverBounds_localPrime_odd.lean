-- Prove2me | Theorems.Thm_ThreeSum_LocalCoverBounds_localPrime_odd
-- name    : ThreeSum.LocalCoverBounds.localPrime_odd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:11:58.945782+00:00
-- url     : https://prove2.me/theorems/acdeefeb-c4ae-4b8a-9016-fa9b1b8ad48c
-- title:
--   Local Cover Bounds: local Prime odd
-- statement:
--   The Local Cover Bounds construction uses the local Prime odd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LocalCoverBounds.lean#L291-L292
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LocalCoverBounds.lean#L291-L292

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

theorem ThreeSum.LocalCoverBounds.localPrime_odd {h : ℕ} (hh : 0 < h) : Odd (localPrime h) := by sorry
