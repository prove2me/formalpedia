-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_auxSource_eq_of_mem_auxSourceWalk_support
-- name    : TreeStack.OrientedBranch.auxSource_eq_of_mem_auxSourceWalk_support
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:19:50.351374+00:00
-- url     : https://prove2.me/theorems/5d856a79-b796-5a79-b6d5-2c7552005d07
-- title:
--   Oriented Branch: aux Source eq of mem aux Source Walk support
-- statement:
--   Every vertex appearing on the canonical source walk has the same canonical
--   source as the walk's starting vertex.  Thus source fibres are path-connected
--   inside the ambient tree.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/HeightSource.lean#L320-L353
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/HeightSource.lean#L320-L353

import Mathlib
import Definitions.Def_TreeStack_LeafSlack
import Definitions.Def_TreeStack_HeightSource
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.OrientedBranch.auxSource_eq_of_mem_auxSourceWalk_support
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    (v x : V)
    (hx : x ∈ (auxSourceWalk C ambientRoot hScores v).2.support) :
    auxSource C ambientRoot hScores x =
      auxSource C ambientRoot hScores v := by sorry
