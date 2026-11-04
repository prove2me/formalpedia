-- Prove2me | Theorems.Thm_ThreeSum_HashFamily_trimmedPairEvent_subset
-- name    : ThreeSum.HashFamily.trimmedPairEvent_subset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:02:59.369252+00:00
-- url     : https://prove2.me/theorems/21673767-8d4b-4987-8d38-01716ff2857d
-- title:
--   Hash Family: trimmed Pair Event subset
-- statement:
--   The Hash Family construction uses the trimmed Pair Event subset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/HashFamily.lean#L706-L709
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/HashFamily.lean#L706-L709

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

theorem ThreeSum.HashFamily.trimmedPairEvent_subset (s t : α → Bool) (a b : K)
    (leftVertices rightVertices : Finset (α → Bool)) (B : ℕ) :
    trimmedPairEvent s t a b leftVertices rightVertices B ⊆ pairEvent s t a b := by sorry
