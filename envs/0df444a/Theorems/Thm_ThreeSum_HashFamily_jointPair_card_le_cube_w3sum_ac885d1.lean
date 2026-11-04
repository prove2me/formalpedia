-- Prove2me | Theorems.Thm_ThreeSum_HashFamily_jointPair_card_le_cube_w3sum_ac885d1
-- name    : ThreeSum.HashFamily.jointPair_card_le_cube_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:02:38.272002+00:00
-- url     : https://prove2.me/theorems/42071ef2-aaf7-4e63-9fb4-31afb7b96288
-- title:
--   Hash Family: joint Pair card le cube
-- statement:
--   Two distinct edges always impose at least three independent hash tests
--   when the left and right vertex classes are disjoint.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/HashFamily.lean#L308-L334
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/HashFamily.lean#L308-L334

import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Dual
import Mathlib.Data.Fin.VecNotation
import Mathlib.GroupTheory.Index
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Push
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Definitions.Def_Submission_ThreeSum_HashFamily
set_option autoImplicit false
open ThreeSum ThreeSum.HashFamily
open scoped BigOperators
variable {α K : Type*}
variable [Fintype α] [DecidableEq α] [Field K] [Fintype K] [DecidableEq K]

theorem ThreeSum.HashFamily.jointPair_card_le_cube_w3sum_ac885d1 {s t u v : α → Bool}
    (hst : s ≠ t) (hsv : s ≠ v) (htu : t ≠ u) (huv : u ≠ v)
    (hpair : (s, t) ≠ (u, v)) (a b : K) :
    Fintype.card K ^ 3 * (pairEvent s t a b ∩ pairEvent u v a b).card ≤
      Fintype.card (α × Bool → K) := by sorry
