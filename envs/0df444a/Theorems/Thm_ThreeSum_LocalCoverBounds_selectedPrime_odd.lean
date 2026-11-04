-- Prove2me | Theorems.Thm_ThreeSum_LocalCoverBounds_selectedPrime_odd
-- name    : ThreeSum.LocalCoverBounds.selectedPrime_odd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:11:46.509896+00:00
-- url     : https://prove2.me/theorems/acc2b0f7-fcf5-4737-9db1-e221d0009dd2
-- title:
--   Local Cover Bounds: selected Prime odd
-- statement:
--   The Local Cover Bounds construction uses the selected Prime odd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LocalCoverBounds.lean#L231-L232
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LocalCoverBounds.lean#L231-L232

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

theorem ThreeSum.LocalCoverBounds.selectedPrime_odd {N : ℕ} (hN : 1 < N) : Odd (selectedPrime N) := by sorry
