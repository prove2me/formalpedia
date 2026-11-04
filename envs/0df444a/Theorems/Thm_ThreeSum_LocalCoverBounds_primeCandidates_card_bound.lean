-- Prove2me | Theorems.Thm_ThreeSum_LocalCoverBounds_primeCandidates_card_bound
-- name    : ThreeSum.LocalCoverBounds.primeCandidates_card_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:11:47.386473+00:00
-- url     : https://prove2.me/theorems/d80915a0-f097-4273-b43c-228609adf493
-- title:
--   Local Cover Bounds: prime Candidates card bound
-- statement:
--   Enumeration of local prime candidates has a direct finite work domain.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LocalCoverBounds.lean#L235-L237
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LocalCoverBounds.lean#L235-L237

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

theorem ThreeSum.LocalCoverBounds.primeCandidates_card_bound (N : ℕ) :
    (primeCandidates N).card ≤ 2 * rootCeiling N + 1 := by sorry
