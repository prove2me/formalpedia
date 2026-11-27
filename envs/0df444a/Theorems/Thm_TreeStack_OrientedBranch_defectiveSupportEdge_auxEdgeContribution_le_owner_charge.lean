-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_defectiveSupportEdge_auxEdgeContribution_le_owner_charge
-- name    : TreeStack.OrientedBranch.defectiveSupportEdge_auxEdgeContribution_le_owner_charge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:09:43.885792+00:00
-- url     : https://prove2.me/theorems/38ebf9dc-5cdb-4224-b0e6-ee14c4fb5682
-- title:
--   Oriented Branch: defective Support Edge aux Edge Contribution le owner charge
-- statement:
--   Every defective retained edge has its weighted contribution bounded by
--   the endpoint baseline plus the charge at its injective rooted owner.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/AuxiliaryCharge.lean#L301-L342
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/AuxiliaryCharge.lean#L301-L342

import Mathlib
import Definitions.Def_TreeStack_Auxiliary
import Definitions.Def_TreeStack_AuxiliaryCharge
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.OrientedBranch.defectiveSupportEdge_auxEdgeContribution_le_owner_charge
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    (B : OrientedBranch T)
    (hDef : B.DefectiveSupportEdge C) :
    auxEdgeContribution C ambientRoot hScores B ≤
      auxWeightInt C ambientRoot hScores B.root +
        auxWeightInt C ambientRoot hScores B.parent +
        auxWeightInt C ambientRoot hScores (B.rootedOwner ambientRoot) *
          scoreDefect T C (B.rootedOwner ambientRoot) := by sorry
