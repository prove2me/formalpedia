-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_defectEdgeState_of_scores_nonpos
-- name    : TreeStack.OrientedBranch.defectEdgeState_of_scores_nonpos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:53:39.04908+00:00
-- url     : https://prove2.me/theorems/585492e1-9c65-5c3d-9d3a-36b5fac5102f
-- title:
--   Oriented Branch: defect Edge State of scores nonpos
-- statement:
--   Concrete TreeStack form of the arbitrary-defect edge classification:
--   for an edge with occupied support on both sides and nonpositive endpoint
--   scores, its two recursive messages lie in one of the exhaustive defect states.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Defect.lean#L261-L278
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Defect.lean#L261-L278

import Mathlib
import Definitions.Def_TreeStack_Obstruction
import Definitions.Def_TreeStack_Defect
set_option autoImplicit false
open TreeStack
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.OrientedBranch.defectEdgeState_of_scores_nonpos
    (C : Configuration V) (B : OrientedBranch T)
    (hB : B.Occupied C)
    (hR : B.reverseBranch.Occupied C)
    (hRoot : score T C B.root ≤ 0)
    (hParent : score T C B.parent ≤ 0) :
    DefectEdgeState
      (messageContribution (branchMessage C B))
      (messageContribution (branchMessage C B.reverseBranch))
      (scoreDefect T C B.root)
      (scoreDefect T C B.parent) := by sorry
