-- Prove2me | Theorems.Thm_ThreeSum_HashFamily_hash_fiber_card
-- name    : ThreeSum.HashFamily.hash_fiber_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:02:31.893343+00:00
-- url     : https://prove2.me/theorems/1d1b6a4d-9d94-4b85-87ab-0ae0c06af1e9
-- title:
--   Hash Family: hash fiber card
-- statement:
--   The exact joint-output count for independent hash coefficient rows.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/HashFamily.lean#L197-L204
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/HashFamily.lean#L197-L204

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

theorem ThreeSum.HashFamily.hash_fiber_card [Fintype K] [DecidableEq K] [DecidableEq σ] [DecidableEq ι]
    {v : ι → σ → K}
    (hv : LinearIndependent K v) (target : ι → K) :
    Fintype.card K ^ Fintype.card ι *
        (Finset.univ.filter (fun w : σ → K => hashMap v w = target)).card =
      Fintype.card K ^ Fintype.card σ := by sorry
