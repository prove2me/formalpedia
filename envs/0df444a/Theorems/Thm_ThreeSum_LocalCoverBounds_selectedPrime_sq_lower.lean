-- Prove2me | Theorems.Thm_ThreeSum_LocalCoverBounds_selectedPrime_sq_lower
-- name    : ThreeSum.LocalCoverBounds.selectedPrime_sq_lower
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:11:43.94811+00:00
-- url     : https://prove2.me/theorems/d79b8864-881a-47c1-925f-d4720b673824
-- title:
--   Local Cover Bounds: selected Prime sq lower
-- statement:
--   The Local Cover Bounds construction uses the selected Prime sq lower property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LocalCoverBounds.lean#L214-L216
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LocalCoverBounds.lean#L214-L216

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

theorem ThreeSum.LocalCoverBounds.selectedPrime_sq_lower (N : ℕ) : N ≤ selectedPrime N ^ 2 := by sorry
