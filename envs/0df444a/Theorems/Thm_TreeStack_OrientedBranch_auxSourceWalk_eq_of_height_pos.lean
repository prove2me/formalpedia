-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_auxSourceWalk_eq_of_height_pos
-- name    : TreeStack.OrientedBranch.auxSourceWalk_eq_of_height_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:14:24.580885+00:00
-- url     : https://prove2.me/theorems/119c9598-5bdd-5e41-805c-d053086ea6b2
-- title:
--   Oriented Branch: aux Source Walk eq of height pos
-- statement:
--   One-step equation for the canonical source walk at positive height.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/HeightSource.lean#L116-L129
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/HeightSource.lean#L116-L129

import Mathlib
import Definitions.Def_TreeStack_LeafSlack
import Definitions.Def_TreeStack_HeightSource
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.OrientedBranch.auxSourceWalk_eq_of_height_pos
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    (v : V) (hPos : 0 < auxHeight C ambientRoot hScores v) :
    auxSourceWalk C ambientRoot hScores v =
      let u := auxParent C ambientRoot hScores v
      let tailCert := auxSourceWalk C ambientRoot hScores u
      ⟨tailCert.1,
        SimpleGraph.Walk.cons
          (auxArrow_adj C ambientRoot
            (auxParent_arrow_of_pos C ambientRoot hScores v hPos)).symm
          tailCert.2⟩ := by sorry
