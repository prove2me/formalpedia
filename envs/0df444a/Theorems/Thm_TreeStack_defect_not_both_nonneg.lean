-- Prove2me | Theorems.Thm_TreeStack_defect_not_both_nonneg
-- name    : TreeStack.defect_not_both_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:52:23.461629+00:00
-- url     : https://prove2.me/theorems/0d065a49-9e3f-489e-bb0c-88350a7d4b82
-- title:
--   Tree Stack: defect not both nonneg
-- statement:
--   Under nonnegative endpoint defects, both edge messages cannot be
--   nonnegative simultaneously.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Defect.lean#L54-L63
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Defect.lean#L54-L63

import Mathlib
import Definitions.Def_TreeStack_Obstruction
import Definitions.Def_TreeStack_Defect
set_option autoImplicit false
open TreeStack

theorem TreeStack.defect_not_both_nonneg
    {a b δu δv : ℤ}
    (hδu : 0 ≤ δu) (hδv : 0 ≤ δv)
    (ha : a = F (-δu - b))
    (hb : b = F (-δv - a)) :
    ¬ (0 ≤ a ∧ 0 ≤ b) := by sorry
