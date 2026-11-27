-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_auxSourceWalk_length
-- name    : TreeStack.OrientedBranch.auxSourceWalk_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:19:48.999539+00:00
-- url     : https://prove2.me/theorems/ff709e11-9e30-4382-b504-ecaf77be99ca
-- title:
--   Oriented Branch: aux Source Walk length
-- statement:
--   The canonical source walk has exactly the recorded auxiliary height.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/HeightSource.lean#L219-L244
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/HeightSource.lean#L219-L244

import Mathlib
import Definitions.Def_TreeStack_LeafSlack
import Definitions.Def_TreeStack_HeightSource
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.OrientedBranch.auxSourceWalk_length
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    (v : V) :
    (auxSourceWalk C ambientRoot hScores v).2.length =
      auxHeight C ambientRoot hScores v := by sorry
