-- Prove2me | Theorems.Thm_TreeStack_two_negative_edge_excess_eq
-- name    : TreeStack.two_negative_edge_excess_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:57:53.901918+00:00
-- url     : https://prove2.me/theorems/1d586575-0cf3-5bb2-8120-0f39bcc8bb58
-- title:
--   Tree Stack: two negative edge excess eq
-- statement:
--   Exact weighted contribution of a two-negative edge in its odd-negative
--   parameterization.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/DefectCharge.lean#L55-L63
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/DefectCharge.lean#L55-L63

import Mathlib
import Definitions.Def_TreeStack_ForestOwner
import Definitions.Def_TreeStack_DefectCharge
set_option autoImplicit false
open TreeStack

theorem TreeStack.two_negative_edge_excess_eq
    {a b r q weightTail weightHead : ℤ}
    (ha : a = -(2 * r + 1))
    (hb : b = -(2 * q + 1)) :
    -(weightHead * a + weightTail * b) =
      weightTail + weightHead +
        2 * (weightHead * r + weightTail * q) := by sorry
