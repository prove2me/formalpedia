-- Prove2me | Theorems.Thm_ThreeSum_HashFamily_tripleEvent_probability
-- name    : ThreeSum.HashFamily.tripleEvent_probability
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:02:45.247783+00:00
-- url     : https://prove2.me/theorems/18c3eb3f-bbe1-4fbb-b819-af25001f6000
-- title:
--   Hash Family: triple Event probability
-- statement:
--   The Hash Family construction uses the triple Event probability property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/HashFamily.lean#L352-L359
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/HashFamily.lean#L352-L359

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

theorem ThreeSum.HashFamily.tripleEvent_probability {s t u : α → Bool}
    (hst : s ≠ t) (hsu : s ≠ u) (htu : t ≠ u) (a b c : K) :
    eventProbability (wordEvent ![s, t, u] ![a, b, c]) =
      1 / (Fintype.card K : ℝ) ^ 3 := by sorry
