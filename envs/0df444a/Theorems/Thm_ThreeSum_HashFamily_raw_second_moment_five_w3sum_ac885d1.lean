-- Prove2me | Theorems.Thm_ThreeSum_HashFamily_raw_second_moment_five_w3sum_ac885d1
-- name    : ThreeSum.HashFamily.raw_second_moment_five_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:02:53.853854+00:00
-- url     : https://prove2.me/theorems/fa060d86-1cca-47f4-b237-eaaee5635d8e
-- title:
--   Hash Family: raw second moment five
-- statement:
--   The paper's coarse `5 lambda` raw second-moment bound follows from
--   explicit graph-size and exceptional-partner inequalities.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/HashFamily.lean#L564-L588
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/HashFamily.lean#L564-L588

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

theorem ThreeSum.HashFamily.raw_second_moment_five_w3sum_ac885d1 (left right : E → α → Bool)
    (hinj : Function.Injective (fun e => (left e, right e)))
    (hcross : ∀ e f, left e ≠ right f)
    (B : ℕ) (hB : ∀ e, (badPartners left right e).card ≤ B)
    (hBp : B ≤ 3 * Fintype.card K) (hEp : Fintype.card E ≤ Fintype.card K ^ 2)
    (a b : K) :
    Fintype.card K ^ 2 *
        (∑ w, incidenceCount (fun e => pairEvent (left e) (right e) a b) w ^ 2) ≤
      5 * Fintype.card E * Fintype.card (α × Bool → K) := by sorry
