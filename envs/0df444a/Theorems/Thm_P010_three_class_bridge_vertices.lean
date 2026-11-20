-- Prove2me | Theorems.Thm_P010_three_class_bridge_vertices
-- name    : P010.three_class_bridge_vertices
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:33:46.44019+00:00
-- url     : https://prove2.me/theorems/eecda2ed-100f-4a67-9181-ec7e43e46785
-- title:
--   P010: three class bridge vertices
-- statement:
--   Class 3 supplies the even endpoint 6 and the bridge endpoint 9
--   when n≥12.
--
--   Source: https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L1080-L1087
-- source:
--   https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L1080-L1087

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
set_option autoImplicit true
@[expose] public section
public section
open P010

theorem P010.three_class_bridge_vertices (n : ℕ) (hn : 12 ≤ n) :
    6 ∈ primeClass n 3 ∧ 9 ∈ primeClass n 3 ∧ 6 ≠ 9 := by sorry
