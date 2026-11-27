-- Prove2me | Theorems.Thm_TreeStack_two_negative_excess_le_owner_budget
-- name    : TreeStack.two_negative_excess_le_owner_budget
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:58:00.917243+00:00
-- url     : https://prove2.me/theorems/4adf7161-f1d2-5e25-868b-d74b244fedb5
-- title:
--   Tree Stack: two negative excess le owner budget
-- statement:
--   If a two-negative edge is oriented toward its owner and owner weight is at
--   least twice tail weight, the complete excess is paid by the owner's endpoint
--   defect.  Here `deltaOwner = q + 2*r` is exactly the local defect equation.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/DefectCharge.lean#L68-L86
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/DefectCharge.lean#L68-L86

import Mathlib
import Definitions.Def_TreeStack_ForestOwner
import Definitions.Def_TreeStack_DefectCharge
set_option autoImplicit false
open TreeStack

theorem TreeStack.two_negative_excess_le_owner_budget
    {r q deltaOwner weightTail weightOwner : ℤ}
    (hq : 0 ≤ q)
    (hDouble : 2 * weightTail ≤ weightOwner)
    (hDelta : deltaOwner = q + 2 * r) :
    2 * (weightOwner * r + weightTail * q) ≤
      weightOwner * deltaOwner := by sorry
