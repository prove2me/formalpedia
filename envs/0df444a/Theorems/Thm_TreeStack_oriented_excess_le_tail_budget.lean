-- Prove2me | Theorems.Thm_TreeStack_oriented_excess_le_tail_budget
-- name    : TreeStack.oriented_excess_le_tail_budget
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:57:39.876455+00:00
-- url     : https://prove2.me/theorems/d802a9d3-c174-434c-915e-10f6613bd0e9
-- title:
--   Tree Stack: oriented excess le tail budget
-- statement:
--   The oriented-edge excess can be paid by the tail endpoint whenever the
--   local defect classification supplies the factor-two tail budget.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/DefectCharge.lean#L35-L42
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/DefectCharge.lean#L35-L42

import Mathlib
import Definitions.Def_TreeStack_ForestOwner
import Definitions.Def_TreeStack_DefectCharge
set_option autoImplicit false
open TreeStack

theorem TreeStack.oriented_excess_le_tail_budget
    {deltaTail deltaHead weightTail : ℤ}
    (hWeight : 0 ≤ weightTail)
    (hBudget : 2 * deltaHead ≤ deltaTail) :
    2 * weightTail * deltaHead ≤ weightTail * deltaTail := by sorry
