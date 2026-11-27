-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_auxSource_auxParent_of_pos
-- name    : TreeStack.OrientedBranch.auxSource_auxParent_of_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:14:33.160786+00:00
-- url     : https://prove2.me/theorems/b63f241f-0069-5da3-adbd-501a04fee65b
-- title:
--   Oriented Branch: aux Source aux Parent of pos
-- statement:
--   At positive height, passing to the canonical predecessor does not change
--   the canonical source.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/HeightSource.lean#L281-L289
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/HeightSource.lean#L281-L289

import Mathlib
import Definitions.Def_TreeStack_LeafSlack
import Definitions.Def_TreeStack_HeightSource
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.OrientedBranch.auxSource_auxParent_of_pos
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    (v : V) (hPos : 0 < auxHeight C ambientRoot hScores v) :
    auxSource C ambientRoot hScores
        (auxParent C ambientRoot hScores v) =
      auxSource C ambientRoot hScores v := by sorry
