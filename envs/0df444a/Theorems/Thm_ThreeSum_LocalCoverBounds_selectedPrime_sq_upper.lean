-- Prove2me | Theorems.Thm_ThreeSum_LocalCoverBounds_selectedPrime_sq_upper
-- name    : ThreeSum.LocalCoverBounds.selectedPrime_sq_upper
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:11:52.564763+00:00
-- url     : https://prove2.me/theorems/1fec77ae-9546-4f99-b86f-28dfeb20dfa7
-- title:
--   Local Cover Bounds: selected Prime sq upper
-- statement:
--   The Local Cover Bounds construction uses the selected Prime sq upper property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LocalCoverBounds.lean#L218-L223
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LocalCoverBounds.lean#L218-L223

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

theorem ThreeSum.LocalCoverBounds.selectedPrime_sq_upper {N : ℕ} (hN : 0 < N) :
    selectedPrime N ^ 2 ≤ 16 * N := by sorry
