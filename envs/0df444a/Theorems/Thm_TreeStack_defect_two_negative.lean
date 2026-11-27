-- Prove2me | Theorems.Thm_TreeStack_defect_two_negative
-- name    : TreeStack.defect_two_negative
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:48:21.71825+00:00
-- url     : https://prove2.me/theorems/7169a889-7b4e-5d2b-bd93-0204ab9b6484
-- title:
--   Tree Stack: defect two negative
-- statement:
--   When both edge messages are negative, they are uniquely of odd negative
--   form and the two endpoint defects are the corresponding linear combinations.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Defect.lean#L67-L109
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Defect.lean#L67-L109

import Mathlib
import Definitions.Def_TreeStack_Obstruction
import Definitions.Def_TreeStack_Defect
set_option autoImplicit false
open TreeStack

theorem TreeStack.defect_two_negative
    {a b δu δv : ℤ}
    (hδu : 0 ≤ δu) (hδv : 0 ≤ δv)
    (ha : a = F (-δu - b))
    (hb : b = F (-δv - a))
    (haNeg : a < 0) (hbNeg : b < 0) :
    ∃ r q : ℤ,
      0 ≤ r ∧ 0 ≤ q ∧
      a = -(2 * r + 1) ∧
      b = -(2 * q + 1) ∧
      δu = r + 2 * q ∧
      δv = q + 2 * r := by sorry
