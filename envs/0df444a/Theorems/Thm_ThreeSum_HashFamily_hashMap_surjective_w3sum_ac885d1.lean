-- Prove2me | Theorems.Thm_ThreeSum_HashFamily_hashMap_surjective_w3sum_ac885d1
-- name    : ThreeSum.HashFamily.hashMap_surjective_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:02:29.576484+00:00
-- url     : https://prove2.me/theorems/c07e86aa-401a-42e4-add6-96264474165f
-- title:
--   Hash Family: hash Map surjective
-- statement:
--   Independent concrete coefficient rows give a surjective hash map.
--   This supplies every target vector; it is not an assumed uniformity property.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/HashFamily.lean#L157-L172
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/HashFamily.lean#L157-L172

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
variable {σ ι : Type*} [Fintype σ] [Fintype ι] [Field K]

theorem ThreeSum.HashFamily.hashMap_surjective_w3sum_ac885d1 {v : ι → σ → K} (hv : LinearIndependent K v) :
    Function.Surjective (hashMap v) := by sorry
