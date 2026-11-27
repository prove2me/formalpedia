-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_auxEdgeContribution_reverse
-- name    : TreeStack.OrientedBranch.auxEdgeContribution_reverse
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:08:09.316225+00:00
-- url     : https://prove2.me/theorems/940fa641-26c6-498e-9d03-e675d96ad6af
-- title:
--   Oriented Branch: aux Edge Contribution reverse
-- statement:
--   The weighted contribution does not depend on which orientation is used to
--   display the underlying edge.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/AuxiliaryCharge.lean#L26-L33
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/AuxiliaryCharge.lean#L26-L33

import Mathlib
import Definitions.Def_TreeStack_Auxiliary
import Definitions.Def_TreeStack_AuxiliaryCharge
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.OrientedBranch.auxEdgeContribution_reverse
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    (B : OrientedBranch T) :
    auxEdgeContribution C ambientRoot hScores B.reverseBranch =
      auxEdgeContribution C ambientRoot hScores B := by sorry
