-- Prove2me | Theorems.Thm_TreeStack_defect_right_budget
-- name    : TreeStack.defect_right_budget
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:00:03.573333+00:00
-- url     : https://prove2.me/theorems/a8e2ad3b-0b44-5506-906b-bcd16ae1f0c0
-- title:
--   Tree Stack: defect right budget
-- statement:
--   Symmetric tail-budget inequality.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Defect.lean#L162-L172
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Defect.lean#L162-L172

import Mathlib
import Definitions.Def_TreeStack_Obstruction
import Definitions.Def_TreeStack_Defect
set_option autoImplicit false
open TreeStack

theorem TreeStack.defect_right_budget
    {a b δu δv : ℤ}
    (hδu : 0 ≤ δu) (hδv : 0 ≤ δv)
    (ha : a = F (-δu - b))
    (hb : b = F (-δv - a))
    (hb0 : 0 ≤ b) :
    2 * δu ≤ δv := by sorry
