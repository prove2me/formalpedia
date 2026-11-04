-- Prove2me | Theorems.Thm_ThreeSum_HashFamily_wordEvent_card
-- name    : ThreeSum.HashFamily.wordEvent_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:02:33.406032+00:00
-- url     : https://prove2.me/theorems/e1be5f1d-e5ae-40e2-bf2e-159f34e0ff81
-- title:
--   Hash Family: word Event card
-- statement:
--   Exact uniform joint count, instantiated with the actual one-hot family.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/HashFamily.lean#L252-L257
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/HashFamily.lean#L252-L257

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

theorem ThreeSum.HashFamily.wordEvent_card {r : ℕ} (words : Fin r → α → Bool) (target : Fin r → K)
    (hwords : LinearIndependent K (fun i => oneHot (K := K) (words i))) :
    Fintype.card K ^ r * (wordEvent words target).card =
      Fintype.card (α × Bool → K) := by sorry
