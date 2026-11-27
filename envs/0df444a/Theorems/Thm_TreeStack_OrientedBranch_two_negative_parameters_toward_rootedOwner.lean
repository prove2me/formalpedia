-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_two_negative_parameters_toward_rootedOwner
-- name    : TreeStack.OrientedBranch.two_negative_parameters_toward_rootedOwner
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:07:09.757154+00:00
-- url     : https://prove2.me/theorems/c14dd5c0-d363-52e8-b9c1-0925c96cfca7
-- title:
--   Oriented Branch: two negative parameters toward rooted Owner
-- statement:
--   In the two-negative state, presenting the edge toward its fixed ambient
--   rooted owner puts the local defect equation in exactly the orientation used by
--   `two_negative_excess_le_owner_budget`.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Auxiliary.lean#L22-L47
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Auxiliary.lean#L22-L47

import Mathlib
import Definitions.Def_TreeStack_DefectCharge
import Definitions.Def_TreeStack_Auxiliary
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.OrientedBranch.two_negative_parameters_toward_rootedOwner
    (C : Configuration V) (ambientRoot : V) (B : OrientedBranch T)
    (hEdge : B.SupportEdge C)
    (hScores : ∀ v, score T C v ≤ 0)
    (haNeg :
      messageContribution (branchMessage C B) < 0)
    (hbNeg :
      messageContribution (branchMessage C B.reverseBranch) < 0)
    (hOwner : B.parent = B.rootedOwner ambientRoot) :
    ∃ r q : ℤ,
      0 ≤ r ∧ 0 ≤ q ∧
      messageContribution (branchMessage C B) = -(2 * r + 1) ∧
      messageContribution (branchMessage C B.reverseBranch) = -(2 * q + 1) ∧
      scoreDefect T C B.root = r + 2 * q ∧
      scoreDefect T C (B.rootedOwner ambientRoot) = q + 2 * r := by sorry
