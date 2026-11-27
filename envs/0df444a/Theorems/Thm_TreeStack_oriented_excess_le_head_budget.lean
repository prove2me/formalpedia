-- Prove2me | Theorems.Thm_TreeStack_oriented_excess_le_head_budget
-- name    : TreeStack.oriented_excess_le_head_budget
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:57:33.349874+00:00
-- url     : https://prove2.me/theorems/7ccc1bb2-f0f7-5b9c-8b66-7b37996692ce
-- title:
--   Tree Stack: oriented excess le head budget
-- statement:
--   The same oriented-edge excess can instead be paid by the head endpoint
--   whenever the auxiliary orientation doubles weights along the edge.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/DefectCharge.lean#L46-L51
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/DefectCharge.lean#L46-L51

import Mathlib
import Definitions.Def_TreeStack_ForestOwner
import Definitions.Def_TreeStack_DefectCharge
set_option autoImplicit false
open TreeStack

theorem TreeStack.oriented_excess_le_head_budget
    {deltaHead weightTail weightHead : ℤ}
    (hDelta : 0 ≤ deltaHead)
    (hDouble : 2 * weightTail ≤ weightHead) :
    2 * weightTail * deltaHead ≤ weightHead * deltaHead := by sorry
