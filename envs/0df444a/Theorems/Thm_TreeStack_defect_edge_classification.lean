-- Prove2me | Theorems.Thm_TreeStack_defect_edge_classification
-- name    : TreeStack.defect_edge_classification
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:52:31.958816+00:00
-- url     : https://prove2.me/theorems/d583d7f6-ffb9-5b48-81ed-ad2a75360d4c
-- title:
--   Tree Stack: defect edge classification
-- statement:
--   Exhaustive arbitrary-defect classification for the two integer messages
--   across a genuine edge.  This is the local algebraic core used by the global
--   defect-flow upper-bound argument.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Defect.lean#L114-L146
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Defect.lean#L114-L146

import Mathlib
import Definitions.Def_TreeStack_Obstruction
import Definitions.Def_TreeStack_Defect
set_option autoImplicit false
open TreeStack

theorem TreeStack.defect_edge_classification
    {a b δu δv : ℤ}
    (hδu : 0 ≤ δu) (hδv : 0 ≤ δv)
    (ha : a = F (-δu - b))
    (hb : b = F (-δv - a)) :
    (0 ≤ a ∧
      b = -2 * (a + δv) - 3 ∧
      (δu = 2 * δv ∨
        (0 < a ∧ δu = 2 * δv + 3))) ∨
    (0 ≤ b ∧
      a = -2 * (b + δu) - 3 ∧
      (δv = 2 * δu ∨
        (0 < b ∧ δv = 2 * δu + 3))) ∨
    ∃ r q : ℤ,
      0 ≤ r ∧ 0 ≤ q ∧
      a = -(2 * r + 1) ∧
      b = -(2 * q + 1) ∧
      δu = r + 2 * q ∧
      δv = q + 2 * r := by sorry
