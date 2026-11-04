-- Prove2me | Theorems.Thm_ThreeSum_HashFamily_hashValue_family
-- name    : ThreeSum.HashFamily.hashValue_family
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:02:31.516191+00:00
-- url     : https://prove2.me/theorems/ab6559dc-3aad-473a-83dd-83737c2b41d2
-- title:
--   Hash Family: hash Value family
-- statement:
--   The Hash Family construction uses the hash Value family property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/HashFamily.lean#L221-L225
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/HashFamily.lean#L221-L225

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

theorem ThreeSum.HashFamily.hashValue_family (v : ι → α → Bool) (w : α × Bool → K)
    [Fintype ι] :
    (fun i => hashValue w (v i)) = hashMap (fun i => oneHot (K := K) (v i)) w := by sorry
