-- Prove2me | Theorems.Thm_ThreeSum_LocalCoverBounds_edgeCount_le_localPrime_sq
-- name    : ThreeSum.LocalCoverBounds.edgeCount_le_localPrime_sq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:12:03.638808+00:00
-- url     : https://prove2.me/theorems/cb995794-90e4-499c-96ff-55dd2aa60d39
-- title:
--   Local Cover Bounds: edge Count le local Prime sq
-- statement:
--   The Local Cover Bounds construction uses the edge Count le local Prime sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LocalCoverBounds.lean#L309-L311
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LocalCoverBounds.lean#L309-L311

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

theorem ThreeSum.LocalCoverBounds.edgeCount_le_localPrime_sq (h : ℕ) :
    outputCount (512 * h) h * groupSize h ≤ localPrime h ^ 2 := by sorry
