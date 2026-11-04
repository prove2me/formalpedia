-- Prove2me | Theorems.Thm_ThreeSum_HashFamily_quadrupleEvent_probability
-- name    : ThreeSum.HashFamily.quadrupleEvent_probability
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:02:42.263478+00:00
-- url     : https://prove2.me/theorems/19036767-1820-40e9-8419-f5d3975c3ec3
-- title:
--   Hash Family: quadruple Event probability
-- statement:
--   The Hash Family construction uses the quadruple Event probability property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/HashFamily.lean#L361-L370
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/HashFamily.lean#L361-L370

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

theorem ThreeSum.HashFamily.quadrupleEvent_probability {s t u v : α → Bool}
    (hst : s ≠ t) (hsu : s ≠ u) (hsv : s ≠ v)
    (htu : t ≠ u) (htv : t ≠ v) (huv : u ≠ v)
    (hm : ∃ i, (s i == t i) ≠ (u i == v i)) (a b c d : K) :
    eventProbability (wordEvent ![s, t, u, v] ![a, b, c, d]) =
      1 / (Fintype.card K : ℝ) ^ 4 := by sorry
