-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_childBranch_vertices_ssubset
-- name    : TreeStack.OrientedBranch.childBranch_vertices_ssubset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:10:32.588518+00:00
-- url     : https://prove2.me/theorems/516f4760-bcba-42f2-8319-5c89cf557b57
-- title:
--   Oriented Branch: child Branch vertices ssubset
-- statement:
--   A genuine child branch is a strict subset of its parent branch.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Branch.lean#L175-L180
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Branch.lean#L175-L180

import Mathlib
import Definitions.Def_TreeStack_Basic
import Definitions.Def_TreeStack_Branch
set_option autoImplicit false
open TreeStack
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.OrientedBranch.childBranch_vertices_ssubset (B : OrientedBranch T) (c : B.Child) :
    (B.childBranch c).vertices ⊂ B.vertices := by sorry
