-- Prove2me | Theorems.Thm_TreeStack_one_vertex_flux_attained_odd
-- name    : TreeStack.one_vertex_flux_attained_odd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:12:15.336931+00:00
-- url     : https://prove2.me/theorems/b6fb1cf7-420d-43b5-8f5d-55ca7d72c0f2
-- title:
--   Tree Stack: one vertex flux attained odd
-- statement:
--   Equality in the one-vertex bound for odd effective input at least three.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Transfer.lean#L114-L125
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Transfer.lean#L114-L125

import Mathlib
import Definitions.Def_TreeStack_Basic
import Definitions.Def_TreeStack_Transfer
set_option autoImplicit false
open TreeStack

theorem TreeStack.one_vertex_flux_attained_odd {k : ℤ} (hk : 1 ≤ k) :
    let y : ℤ := 2 * k + 1
    let A : ℤ := k + 1
    let B : ℤ := 1
    1 ≤ A ∧ 0 ≤ B ∧ y + B - 2 * A = 0 ∧ A - 2 * B = F y := by sorry
