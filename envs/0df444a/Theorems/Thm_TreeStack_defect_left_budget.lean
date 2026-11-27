-- Prove2me | Theorems.Thm_TreeStack_defect_left_budget
-- name    : TreeStack.defect_left_budget
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:47:29.43261+00:00
-- url     : https://prove2.me/theorems/792512af-4a8c-553d-afa3-16b058b36f19
-- title:
--   Tree Stack: defect left budget
-- statement:
--   In the oriented case, the tail defect always has enough budget to pay
--   twice the head defect.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Defect.lean#L150-L159
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Defect.lean#L150-L159

import Mathlib
import Definitions.Def_TreeStack_Obstruction
import Definitions.Def_TreeStack_Defect
set_option autoImplicit false
open TreeStack

theorem TreeStack.defect_left_budget
    {a b δu δv : ℤ}
    (hδu : 0 ≤ δu) (hδv : 0 ≤ δv)
    (ha : a = F (-δu - b))
    (hb : b = F (-δv - a))
    (ha0 : 0 ≤ a) :
    2 * δv ≤ δu := by sorry
