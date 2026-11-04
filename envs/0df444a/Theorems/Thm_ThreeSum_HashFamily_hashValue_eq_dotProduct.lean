-- Prove2me | Theorems.Thm_ThreeSum_HashFamily_hashValue_eq_dotProduct
-- name    : ThreeSum.HashFamily.hashValue_eq_dotProduct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:02:29.167779+00:00
-- url     : https://prove2.me/theorems/55fafdc0-a311-48e7-a77e-750c184fcdeb
-- title:
--   Hash Family: hash Value eq dot Product
-- statement:
--   The Hash Family construction uses the hash Value eq dot Product property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/HashFamily.lean#L216-L219
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/HashFamily.lean#L216-L219

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
variable {ι : Type*} [Fintype α] [Field K]

theorem ThreeSum.HashFamily.hashValue_eq_dotProduct (w : α × Bool → K) (s : α → Bool) :
    hashValue w s = ∑ p, oneHot (K := K) s p * w p := by sorry
