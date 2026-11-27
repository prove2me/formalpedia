-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_defect_equations_of_both_occupied
-- name    : TreeStack.OrientedBranch.defect_equations_of_both_occupied
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:46:43.08727+00:00
-- url     : https://prove2.me/theorems/994d94b5-40f7-5426-8979-baa96faaa141
-- title:
--   Oriented Branch: defect equations of both occupied
-- statement:
--   On an edge whose two sides are both occupied, the actual recursive branch
--   messages satisfy exactly the abstract defect equations used by the global
--   defect-flow argument.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Defect.lean#L220-L256
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Defect.lean#L220-L256

import Mathlib
import Definitions.Def_TreeStack_Obstruction
import Definitions.Def_TreeStack_Defect
set_option autoImplicit false
open TreeStack
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.OrientedBranch.defect_equations_of_both_occupied
    (C : Configuration V) (B : OrientedBranch T)
    (hB : B.Occupied C)
    (hR : B.reverseBranch.Occupied C) :
    let a :=
      messageContribution (branchMessage C B)
    let b :=
      messageContribution (branchMessage C B.reverseBranch)
    let δu := scoreDefect T C B.root
    let δv := scoreDefect T C B.parent
    a = F (-δu - b) ∧
      b = F (-δv - a) := by sorry
