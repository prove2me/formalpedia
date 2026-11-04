-- Prove2me | Theorems.Thm_ThreeSum_HashFamily_raw_first_moment
-- name    : ThreeSum.HashFamily.raw_first_moment
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:02:54.546219+00:00
-- url     : https://prove2.me/theorems/074ef812-ea0e-4880-aacd-dd583d1b5701
-- title:
--   Hash Family: raw first moment
-- statement:
--   The raw first moment for a concrete finite graph of one-hot endpoints.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/HashFamily.lean#L470-L477
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/HashFamily.lean#L470-L477

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
variable {E : Type*} [Fintype E] [DecidableEq E]
variable [Fintype α] [DecidableEq α] [Field K] [Fintype K] [DecidableEq K]

theorem ThreeSum.HashFamily.raw_first_moment (left right : E → α → Bool)
    (hcross : ∀ e f, left e ≠ right f) (a b : K) :
    Fintype.card K ^ 2 *
        (∑ w, incidenceCount (fun e => pairEvent (left e) (right e) a b) w) =
      Fintype.card E * Fintype.card (α × Bool → K) := by sorry
