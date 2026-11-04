-- Prove2me | Theorems.Thm_ThreeSum_HashFamily_pairEvent_probability
-- name    : ThreeSum.HashFamily.pairEvent_probability
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:02:43.459895+00:00
-- url     : https://prove2.me/theorems/34c5d6be-0402-439a-93b1-c3400740d648
-- title:
--   Hash Family: pair Event probability
-- statement:
--   A pair of distinct actual endpoint words hashes uniformly, including
--   when the two requested target residues are equal.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/HashFamily.lean#L280-L286
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/HashFamily.lean#L280-L286

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

theorem ThreeSum.HashFamily.pairEvent_probability {s t : α → Bool} (hst : s ≠ t) (a b : K) :
    eventProbability (pairEvent s t a b) = 1 / (Fintype.card K : ℝ) ^ 2 := by sorry
