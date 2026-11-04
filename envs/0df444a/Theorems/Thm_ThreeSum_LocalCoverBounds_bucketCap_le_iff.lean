-- Prove2me | Theorems.Thm_ThreeSum_LocalCoverBounds_bucketCap_le_iff
-- name    : ThreeSum.LocalCoverBounds.bucketCap_le_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:12:06.452214+00:00
-- url     : https://prove2.me/theorems/159ac0bd-f9a1-4e4f-9bcc-d83a0e0020a4
-- title:
--   Local Cover Bounds: bucket Cap le iff
-- statement:
--   The Local Cover Bounds construction uses the bucket Cap le iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LocalCoverBounds.lean#L247-L250
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LocalCoverBounds.lean#L247-L250

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

theorem ThreeSum.LocalCoverBounds.bucketCap_le_iff {V p b : ℕ} (hp : 0 < p) :
    bucketCap V p ≤ b ↔ 4 * (p + V) ≤ b * p := by sorry
