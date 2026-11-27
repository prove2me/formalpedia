-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_auxEdgeContribution_eq_emptySide_charge
-- name    : TreeStack.OrientedBranch.auxEdgeContribution_eq_emptySide_charge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:10:08.618946+00:00
-- url     : https://prove2.me/theorems/0378e636-fa76-42b2-a639-3e91b481fcec
-- title:
--   Oriented Branch: aux Edge Contribution eq empty Side charge
-- statement:
--   Across a nonretained edge with an occupied displayed root side, the other
--   message remains literally `EMPTY`.  The whole weighted edge contribution is
--   exactly the defect charge at the empty-side endpoint, whose auxiliary weight
--   is one.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/AuxiliaryCharge.lean#L372-L395
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/AuxiliaryCharge.lean#L372-L395

import Mathlib
import Definitions.Def_TreeStack_Auxiliary
import Definitions.Def_TreeStack_AuxiliaryCharge
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.OrientedBranch.auxEdgeContribution_eq_emptySide_charge
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    (B : OrientedBranch T)
    (hOccupied : B.Occupied C)
    (hEmpty : ¬ B.reverseBranch.Occupied C) :
    auxEdgeContribution C ambientRoot hScores B =
      auxWeightInt C ambientRoot hScores B.parent *
        scoreDefect T C B.parent := by sorry
