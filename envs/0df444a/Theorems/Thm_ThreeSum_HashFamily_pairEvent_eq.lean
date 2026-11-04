-- Prove2me | Theorems.Thm_ThreeSum_HashFamily_pairEvent_eq
-- name    : ThreeSum.HashFamily.pairEvent_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:02:37.69258+00:00
-- url     : https://prove2.me/theorems/3385d797-f625-4ff4-903f-0d5fcc98432d
-- title:
--   Hash Family: pair Event eq
-- statement:
--   The Hash Family construction uses the pair Event eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/HashFamily.lean#L273-L276
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/HashFamily.lean#L273-L276

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

theorem ThreeSum.HashFamily.pairEvent_eq (s t : α → Bool) (a b : K) :
    pairEvent s t a b = wordEvent ![s, t] ![a, b] := by sorry
