-- Prove2me | Theorems.Thm_ThreeSum_HashFamily_linear_fiber_card_w3sum_ac885d1
-- name    : ThreeSum.HashFamily.linear_fiber_card_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:02:29.287249+00:00
-- url     : https://prove2.me/theorems/598220a1-7491-48b0-b518-708aac625126
-- title:
--   Hash Family: linear fiber card
-- statement:
--   Equal-sized fibers of a surjective linear map, with the full sample
--   space cardinality on the right. This exact integer equality is the finite
--   uniform-distribution statement used in the hash moments.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/HashFamily.lean#L177-L194
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/HashFamily.lean#L177-L194

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

theorem ThreeSum.HashFamily.linear_fiber_card_w3sum_ac885d1 {V W : Type*} [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [Fintype V] [Fintype W] [DecidableEq W]
    (f : V →ₗ[K] W) (hf : Function.Surjective f) (target : W) :
    Fintype.card W * (Finset.univ.filter (fun x => f x = target)).card =
      Fintype.card V := by sorry
