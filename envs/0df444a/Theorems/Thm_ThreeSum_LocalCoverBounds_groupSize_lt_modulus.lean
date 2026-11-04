-- Prove2me | Theorems.Thm_ThreeSum_LocalCoverBounds_groupSize_lt_modulus
-- name    : ThreeSum.LocalCoverBounds.groupSize_lt_modulus
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:11:36.872196+00:00
-- url     : https://prove2.me/theorems/65878194-dd36-4542-8947-da088086c223
-- title:
--   Local Cover Bounds: group Size lt modulus
-- statement:
--   The Local Cover Bounds construction uses the group Size lt modulus property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LocalCoverBounds.lean#L107-L118
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LocalCoverBounds.lean#L107-L118

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

theorem ThreeSum.LocalCoverBounds.groupSize_lt_modulus {L h p : ℕ}
    (hM : 2 ^ (2 * h) < outputCount L h)
    (hp : outputCount L h * 2 ^ (2 * h) ≤ p ^ 2) : groupSize h < p := by sorry
