-- Prove2me | Theorems.Thm_TreeStack_one_vertex_flux_attained_even
-- name    : TreeStack.one_vertex_flux_attained_even
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:12:19.519859+00:00
-- url     : https://prove2.me/theorems/f44e7628-c8eb-46c9-84a7-e1cc84a3654d
-- title:
--   Tree Stack: one vertex flux attained even
-- statement:
--   Equality in the one-vertex bound for positive even effective input.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Transfer.lean#L101-L111
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Transfer.lean#L101-L111

import Mathlib
import Definitions.Def_TreeStack_Basic
import Definitions.Def_TreeStack_Transfer
set_option autoImplicit false
open TreeStack

theorem TreeStack.one_vertex_flux_attained_even {k : ℤ} (hk : 1 ≤ k) :
    let y : ℤ := 2 * k
    let A : ℤ := k
    let B : ℤ := 0
    1 ≤ A ∧ 0 ≤ B ∧ y + B - 2 * A = 0 ∧ A - 2 * B = F y := by sorry
