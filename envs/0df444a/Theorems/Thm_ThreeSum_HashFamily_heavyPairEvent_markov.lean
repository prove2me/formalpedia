-- Prove2me | Theorems.Thm_ThreeSum_HashFamily_heavyPairEvent_markov
-- name    : ThreeSum.HashFamily.heavyPairEvent_markov
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:02:56.513443+00:00
-- url     : https://prove2.me/theorems/3605bdf1-b920-47cc-83be-a4457f07f146
-- title:
--   Hash Family: heavy Pair Event markov
-- statement:
--   Finite Markov counting, with the actual bucket cardinality.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/HashFamily.lean#L663-L675
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/HashFamily.lean#L663-L675

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

theorem ThreeSum.HashFamily.heavyPairEvent_markov (s t : α → Bool) (a b : K)
    (vertices : Finset (α → Bool)) (B : ℕ) :
    B * (heavyPairEvent s t a b vertices B).card ≤ loadedPairMass s t a b vertices := by sorry
