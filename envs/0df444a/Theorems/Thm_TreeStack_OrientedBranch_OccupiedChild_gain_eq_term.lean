-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_OccupiedChild_gain_eq_term
-- name    : TreeStack.OrientedBranch.OccupiedChild.gain_eq_term
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:30:07.912614+00:00
-- url     : https://prove2.me/theorems/fc90173e-5071-5af1-aef1-cc2110ed8520
-- title:
--   Occupied Child: gain eq term
-- statement:
--   The Occupied Child construction uses the gain eq term property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Boundary.lean#L890-L896
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Boundary.lean#L890-L896

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

theorem TreeStack.OrientedBranch.OccupiedChild.gain_eq_term
    {B : OrientedBranch T} {C : Configuration V}
    (t : B.OccupiedChild C) :
    t.gain = B.childMessageTerm C t.1 := by sorry
