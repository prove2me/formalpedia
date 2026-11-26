-- Prove2me | Theorems.Thm_Scott1976_DataTypesAsLattices_theorem_3_2
-- name    : Scott1976.DataTypesAsLattices.theorem_3_2
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:00:11.449874+00:00
-- url     : https://prove2.me/theorems/53bca8a9-7bef-476a-9931-17cd9ab1ff4e
-- title:
--   Data Types As Lattices: theorem 3 2
-- statement:
--   **Scott 1976, Theorem 3.2 (The enumeration theorem), generation half.**
--
--   Source: https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Enumeration.lean#L55-L58
-- source:
--   https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Enumeration.lean#L55-L58

import Definitions.Def_Scott1976_DataTypesAsLattices_Computability
import Definitions.Def_Scott1976_DataTypesAsLattices_Enumeration
set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices

theorem Scott1976.DataTypesAsLattices.theorem_3_2 :
    zeroC ∈ RE ∧ sucC ∈ RE ∧ predC ∈ RE ∧ condC ∈ RE ∧
      Kcomb ∈ RE ∧ Scomb ∈ RE := by sorry
