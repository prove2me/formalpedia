-- Prove2me | Theorems.Thm_ThreeSum_HashFamily_jointPair_card_four
-- name    : ThreeSum.HashFamily.jointPair_card_four
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:02:40.521616+00:00
-- url     : https://prove2.me/theorems/3e6e51ba-89d2-4215-b5d7-0f3d84ee87ec
-- title:
--   Hash Family: joint Pair card four
-- statement:
--   The Hash Family construction uses the joint Pair card four property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/HashFamily.lean#L336-L350
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/HashFamily.lean#L336-L350

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

theorem ThreeSum.HashFamily.jointPair_card_four {s t u v : α → Bool}
    (hst : s ≠ t) (hsu : s ≠ u) (hsv : s ≠ v)
    (htu : t ≠ u) (htv : t ≠ v) (huv : u ≠ v)
    (hm : ∃ i, (s i == t i) ≠ (u i == v i)) (a b : K) :
    Fintype.card K ^ 4 * (pairEvent s t a b ∩ pairEvent u v a b).card =
      Fintype.card (α × Bool → K) := by sorry
