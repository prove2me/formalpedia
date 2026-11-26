-- Prove2me | Theorems.Thm_Scott1976_DataTypesAsLattices_theorem_3_6
-- name    : Scott1976.DataTypesAsLattices.theorem_3_6
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:00:25.349152+00:00
-- url     : https://prove2.me/theorems/88cc1c1a-50fa-466a-99e9-d7f94fdd096e
-- title:
--   Data Types As Lattices: theorem 3 6
-- statement:
--   **Scott 1976, Theorem 3.6 (The subalgebra theorem), generation.**
--
--   Source: https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Enumeration.lean#L135-L146
-- source:
--   https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Enumeration.lean#L135-L146

import Definitions.Def_Scott1976_DataTypesAsLattices_Computability
import Definitions.Def_Scott1976_DataTypesAsLattices_Enumeration
set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices

theorem Scott1976.DataTypesAsLattices.theorem_3_6 (a : Pomega) :
    (∀ u ∈ RE, funOf u a ∈ Deg a) ∧
      (∀ x y, x ∈ Deg a → y ∈ Deg a →
        ∃ r s, IsCombinatory r ∧ IsCombinatory s ∧
          x = funOf r a ∧ y = funOf s a) := by sorry
