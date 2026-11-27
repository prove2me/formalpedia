-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_score_eq_effectiveInput_add_reverse
-- name    : TreeStack.OrientedBranch.score_eq_effectiveInput_add_reverse
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:45:46.110677+00:00
-- url     : https://prove2.me/theorems/f07c1df2-ccef-5cb4-a17e-d92c7ec3a2e0
-- title:
--   Oriented Branch: score eq effective Input add reverse
-- statement:
--   A rooted score at the root of an oriented branch splits into the branch's
--   effective input from its genuine children plus the message from the reverse
--   (parent-side) branch.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Obstruction.lean#L767-L807
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Obstruction.lean#L767-L807

import Mathlib
import Definitions.Def_TreeStack_Estimator
import Definitions.Def_TreeStack_RootScore
import Definitions.Def_TreeStack_Obstruction
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
variable {V : Type*} [Fintype V] {T : FiniteTree V}
open TreeStack.OrientedBranch

theorem TreeStack.OrientedBranch.score_eq_effectiveInput_add_reverse
    (C : Configuration V) (B : OrientedBranch T) :
    score T C B.root =
      B.effectiveInput C +
        messageContribution (branchMessage C B.reverseBranch) := by sorry
