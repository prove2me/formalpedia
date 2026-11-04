-- Prove2me | Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
-- name    : ThreeSum.HashFamily.hashMap_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:02:29.497895+00:00
-- url     : https://prove2.me/theorems/176e0bc0-4d52-4333-8c3d-141adfb3e64d
-- title:
--   Hash Family: hash Map apply
-- statement:
--   The Hash Family construction uses the hash Map apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/HashFamily.lean#L150-L153
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/HashFamily.lean#L150-L153

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

theorem ThreeSum.HashFamily.hashMap_apply (v : ι → σ → K) (w : σ → K) (i : ι) :
    hashMap v w i = ∑ x, v i x * w x := by sorry
