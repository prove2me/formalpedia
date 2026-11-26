-- Prove2me | Theorems.Thm_Scott1976_DataTypesAsLattices_theorem_3_4
-- name    : Scott1976.DataTypesAsLattices.theorem_3_4
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:00:15.865229+00:00
-- url     : https://prove2.me/theorems/51db99d6-7465-43d4-a631-c8202bc848b6
-- title:
--   Data Types As Lattices: theorem 3 4
-- statement:
--   **Scott 1976, Theorem 3.4 (The incompleteness theorem), diagonal form.**
--
--   Source: https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Enumeration.lean#L73-L108
-- source:
--   https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Enumeration.lean#L73-L108

import Definitions.Def_Scott1976_DataTypesAsLattices_Computability
import Definitions.Def_Scott1976_DataTypesAsLattices_Enumeration
set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices

theorem Scott1976.DataTypesAsLattices.theorem_3_4 {val : ℕ → Pomega} {v : ℕ → ℕ} {b : Set ℕ}
    (hv : ∀ k, val (v k) = ofNat k ∩ val k)
    (hb : b = {j | val j = botElem})
    (hex : ∃ k, val k = {i | v i ∈ b}) : False := by sorry
