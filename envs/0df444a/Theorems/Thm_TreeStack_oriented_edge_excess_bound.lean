-- Prove2me | Theorems.Thm_TreeStack_oriented_edge_excess_bound
-- name    : TreeStack.oriented_edge_excess_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:57:13.496833+00:00
-- url     : https://prove2.me/theorems/7ca608a5-8ef5-409a-9d05-e64b18b33a8d
-- title:
--   Tree Stack: oriented edge excess bound
-- statement:
--   Weighted edge estimate for an oriented-type defect edge.  If the auxiliary
--   weight at the head is at least twice the weight at the tail, the edge
--   contribution is bounded by the neutral endpoint weights plus the standard
--   head-defect excess.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/DefectCharge.lean#L10-L31
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/DefectCharge.lean#L10-L31

import Mathlib
import Definitions.Def_TreeStack_ForestOwner
import Definitions.Def_TreeStack_DefectCharge
set_option autoImplicit false
open TreeStack

theorem TreeStack.oriented_edge_excess_bound
    {a b deltaHead weightTail weightHead : ℤ}
    (ha : 0 ≤ a)
    (hb : b = -2 * (a + deltaHead) - 3)
    (hDouble : 2 * weightTail ≤ weightHead) :
    -(weightHead * a + weightTail * b) ≤
      weightTail + weightHead + 2 * weightTail * deltaHead := by sorry
