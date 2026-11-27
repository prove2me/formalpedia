-- Prove2me | Theorems.Thm_TreeStack_defect_left_nonneg
-- name    : TreeStack.defect_left_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:46:38.741388+00:00
-- url     : https://prove2.me/theorems/66aaf0cb-513e-5562-8020-519fb5a98e16
-- title:
--   Tree Stack: defect left nonneg
-- statement:
--   If the message from `u` to `v` is nonnegative, then the reverse
--   message is forced negative and the tail defect is either exactly twice the
--   head defect or three more than twice the head defect.  The latter alternative
--   requires a strictly positive forward message.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Defect.lean#L10-L35
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Defect.lean#L10-L35

import Mathlib
import Definitions.Def_TreeStack_Obstruction
import Definitions.Def_TreeStack_Defect
set_option autoImplicit false
open TreeStack

theorem TreeStack.defect_left_nonneg
    {a b δu δv : ℤ}
    (hδu : 0 ≤ δu) (hδv : 0 ≤ δv)
    (ha : a = F (-δu - b))
    (hb : b = F (-δv - a))
    (ha0 : 0 ≤ a) :
    b = -2 * (a + δv) - 3 ∧
      (δu = 2 * δv ∨
        (0 < a ∧ δu = 2 * δv + 3)) := by sorry
