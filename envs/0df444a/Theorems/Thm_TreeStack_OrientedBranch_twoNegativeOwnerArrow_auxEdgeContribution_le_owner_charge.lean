-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_twoNegativeOwnerArrow_auxEdgeContribution_le_owner_charge
-- name    : TreeStack.OrientedBranch.twoNegativeOwnerArrow_auxEdgeContribution_le_owner_charge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:08:59.881654+00:00
-- url     : https://prove2.me/theorems/164b7aca-a3c8-4e09-8574-129daf4f05cd
-- title:
--   Oriented Branch: two Negative Owner Arrow aux Edge Contribution le owner charge
-- statement:
--   A defective two-negative edge directed toward its rooted owner has its
--   entire weighted excess payable by the owner endpoint defect.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/AuxiliaryCharge.lean#L125-L166
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/AuxiliaryCharge.lean#L125-L166

import Mathlib
import Definitions.Def_TreeStack_Auxiliary
import Definitions.Def_TreeStack_AuxiliaryCharge
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.OrientedBranch.twoNegativeOwnerArrow_auxEdgeContribution_le_owner_charge
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    (B : OrientedBranch T)
    (hTwo : B.TwoNegativeOwnerArrow C ambientRoot) :
    auxEdgeContribution C ambientRoot hScores B ≤
      auxWeightInt C ambientRoot hScores B.root +
        auxWeightInt C ambientRoot hScores B.parent +
        auxWeightInt C ambientRoot hScores B.parent *
          scoreDefect T C B.parent := by sorry
