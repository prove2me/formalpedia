-- Prove2me | Theorems.Thm_TreeStack_stackable_of_step
-- name    : TreeStack.stackable_of_step
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:06:41.566783+00:00
-- url     : https://prove2.me/theorems/84c971ce-cb93-4a60-8b18-4112771fac0a
-- title:
--   Tree Stack: stackable of step
-- statement:
--   Stackability is preserved when one legal move is prefixed.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/PebblingMove.lean#L66-L70
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/PebblingMove.lean#L66-L70

import Mathlib
import Definitions.Def_TreeStack_Basic
import Definitions.Def_TreeStack_PebblingMove
set_option autoImplicit false
open TreeStack

theorem TreeStack.stackable_of_step {V : Type*} [DecidableEq V]
    {G : SimpleGraph V} {C D : Configuration V}
    (hCD : PebbleStep G C D) (hD : Stackable G D) : Stackable G C := by sorry
