-- Prove2me | Theorems.Thm_Scott1976_DataTypesAsLattices_theorem_3_5
-- name    : Scott1976.DataTypesAsLattices.theorem_3_5
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:00:14.71282+00:00
-- url     : https://prove2.me/theorems/bf1f79bb-e883-59d5-b8be-0121df345d82
-- title:
--   Data Types As Lattices: theorem 3 5
-- statement:
--   **Scott 1976, Theorem 3.5 (The completeness theorem for definability),
--   realizer form.** If `q` realizes `p` on values, then `val(p n) = q(val n)`.
--
--   Source: https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Enumeration.lean#L126-L128
-- source:
--   https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Enumeration.lean#L126-L128

import Definitions.Def_Scott1976_DataTypesAsLattices_Computability
import Definitions.Def_Scott1976_DataTypesAsLattices_Enumeration
set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices

theorem Scott1976.DataTypesAsLattices.theorem_3_5 {val : ℕ → Pomega} {p : ℕ → ℕ} {q : Pomega}
    (hq : ∀ n, val (p n) = funOf q (val n)) :
    ∀ n, val (p n) = funOf q (val n) := by sorry
