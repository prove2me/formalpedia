-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_auxiliaryState_auxEdgeContribution_le_rootedOwner_charge
-- name    : TreeStack.OrientedBranch.auxiliaryState_auxEdgeContribution_le_rootedOwner_charge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:08:58.351877+00:00
-- url     : https://prove2.me/theorems/a50e6512-dde0-5c4b-93ec-9af7e7741f68
-- title:
--   Oriented Branch: auxiliary State aux Edge Contribution le rooted Owner charge
-- statement:
--   For a displayed auxiliary edge state, the weighted excess is payable by
--   the fixed rooted owner of the underlying edge.  This is the local statement
--   that the future global sum will combine with injectivity of `rootedOwner`.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/AuxiliaryCharge.lean#L171-L200
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/AuxiliaryCharge.lean#L171-L200

import Mathlib
import Definitions.Def_TreeStack_Auxiliary
import Definitions.Def_TreeStack_AuxiliaryCharge
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.OrientedBranch.auxiliaryState_auxEdgeContribution_le_rootedOwner_charge
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    (B : OrientedBranch T)
    (hState :
      (B.DefectiveSupportEdge C ∧ B.DefectArrow C) ∨
        B.TwoNegativeOwnerArrow C ambientRoot) :
    auxEdgeContribution C ambientRoot hScores B ≤
      auxWeightInt C ambientRoot hScores B.root +
        auxWeightInt C ambientRoot hScores B.parent +
        auxWeightInt C ambientRoot hScores (B.rootedOwner ambientRoot) *
          scoreDefect T C (B.rootedOwner ambientRoot) := by sorry
