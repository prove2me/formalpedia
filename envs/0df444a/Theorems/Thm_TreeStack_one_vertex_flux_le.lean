-- Prove2me | Theorems.Thm_TreeStack_one_vertex_flux_le
-- name    : TreeStack.one_vertex_flux_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:11:40.751998+00:00
-- url     : https://prove2.me/theorems/f820f7f2-f25b-473b-81c9-ee8c5d9e926b
-- title:
--   Tree Stack: one vertex flux le
-- statement:
--   The one-vertex signature inequality. `A` counts outward moves and is
--   positive; `B` counts inward moves.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Transfer.lean#L77-L81
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Transfer.lean#L77-L81

import Mathlib
import Definitions.Def_TreeStack_Basic
import Definitions.Def_TreeStack_Transfer
set_option autoImplicit false
open TreeStack

theorem TreeStack.one_vertex_flux_le {y A B : ℤ}
    (hA : 1 ≤ A) (hB : 0 ≤ B) (hbal : y + B - 2 * A = 0) :
    A - 2 * B ≤ F y := by sorry
