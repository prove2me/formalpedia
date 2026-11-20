-- Prove2me | Theorems.Thm_P010_orderedPrimeClass_head
-- name    : P010.orderedPrimeClass_head
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:28:34.844173+00:00
-- url     : https://prove2.me/theorems/0ac8a6a0-15b5-4042-8ada-4a3702106a0c
-- title:
--   P010: ordered Prime Class head
-- statement:
--   The prescribed path starts at u.
--
--   Source: https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L1157-L1159
-- source:
--   https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L1157-L1159

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
set_option autoImplicit true
@[expose] public section
public section
open P010

theorem P010.orderedPrimeClass_head (n p u v : ℕ) :
    (orderedPrimeClass n p u v).head? = some u := by sorry
