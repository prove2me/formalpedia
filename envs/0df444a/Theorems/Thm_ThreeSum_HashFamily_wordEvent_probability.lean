-- Prove2me | Theorems.Thm_ThreeSum_HashFamily_wordEvent_probability
-- name    : ThreeSum.HashFamily.wordEvent_probability
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:02:36.198218+00:00
-- url     : https://prove2.me/theorems/657c8c40-fa55-4fce-9a34-f674dac83aed
-- title:
--   Hash Family: word Event probability
-- statement:
--   The Hash Family construction uses the word Event probability property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/HashFamily.lean#L259-L268
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/HashFamily.lean#L259-L268

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

theorem ThreeSum.HashFamily.wordEvent_probability {r : ℕ} (words : Fin r → α → Bool) (target : Fin r → K)
    (hwords : LinearIndependent K (fun i => oneHot (K := K) (words i))) :
    eventProbability (wordEvent words target) = 1 / (Fintype.card K : ℝ) ^ r := by sorry
