-- Prove2me | Theorems.Thm_TreeStack_defect_right_nonneg
-- name    : TreeStack.defect_right_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:52:15.409875+00:00
-- url     : https://prove2.me/theorems/ce5e3a48-1f1a-56c5-97bb-4855d2dcb3f1
-- title:
--   Tree Stack: defect right nonneg
-- statement:
--   Symmetric form of `defect_left_nonneg`.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Defect.lean#L38-L50
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Defect.lean#L38-L50

import Mathlib
import Definitions.Def_TreeStack_Obstruction
import Definitions.Def_TreeStack_Defect
set_option autoImplicit false
open TreeStack

theorem TreeStack.defect_right_nonneg
    {a b δu δv : ℤ}
    (hδu : 0 ≤ δu) (hδv : 0 ≤ δv)
    (ha : a = F (-δu - b))
    (hb : b = F (-δv - a))
    (hb0 : 0 ≤ b) :
    a = -2 * (b + δu) - 3 ∧
      (δv = 2 * δu ∨
        (0 < b ∧ δv = 2 * δu + 3)) := by sorry
