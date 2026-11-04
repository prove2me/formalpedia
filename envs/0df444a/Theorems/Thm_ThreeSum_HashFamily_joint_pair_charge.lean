-- Prove2me | Theorems.Thm_ThreeSum_HashFamily_joint_pair_charge
-- name    : ThreeSum.HashFamily.joint_pair_charge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:02:51.690964+00:00
-- url     : https://prove2.me/theorems/b08273a7-e44a-4b17-a4fd-dfdf784ca6d2
-- title:
--   Hash Family: joint pair charge
-- statement:
--   The Hash Family construction uses the joint pair charge property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/HashFamily.lean#L479-L519
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/HashFamily.lean#L479-L519

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

theorem ThreeSum.HashFamily.joint_pair_charge (left right : E → α → Bool)
    (hinj : Function.Injective (fun e => (left e, right e)))
    (hcross : ∀ e f, left e ≠ right f) (a b : K) (e f : E) :
    Fintype.card K ^ 4 *
        (pairEvent (left e) (right e) a b ∩ pairEvent (left f) (right f) a b).card ≤
      Fintype.card (α × Bool → K) *
        (1 + (if e = f then Fintype.card K ^ 2 else 0) +
          (if f ∈ badPartners left right e then Fintype.card K else 0)) := by sorry
