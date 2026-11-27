-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_OccupiedChild_gain_eq_F
-- name    : TreeStack.OrientedBranch.OccupiedChild.gain_eq_F
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:30:00.346065+00:00
-- url     : https://prove2.me/theorems/13aad3c9-5e37-5415-913c-cb1a21f4f78d
-- title:
--   Occupied Child: gain eq F
-- statement:
--   The Occupied Child construction uses the gain eq F property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Boundary.lean#L882-L888
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Boundary.lean#L882-L888

import Mathlib
import Definitions.Def_TreeStack_PebblingMove
import Definitions.Def_TreeStack_Message
import Definitions.Def_TreeStack_Boundary
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}
variable [DecidableEq V]

theorem TreeStack.OrientedBranch.OccupiedChild.gain_eq_F
    {B : OrientedBranch T} {C : Configuration V}
    (t : B.OccupiedChild C) :
    t.gain = F (effectiveInput C (B.childBranch t.child)) := by sorry
