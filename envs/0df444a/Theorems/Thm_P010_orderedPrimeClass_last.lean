-- Prove2me | Theorems.Thm_P010_orderedPrimeClass_last
-- name    : P010.orderedPrimeClass_last
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:28:36.758207+00:00
-- url     : https://prove2.me/theorems/c59e20cf-d7ba-423b-ac2f-ca46018a7a76
-- title:
--   P010: ordered Prime Class last
-- statement:
--   The prescribed path ends at v.
--
--   Source: https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L1162-L1167
-- source:
--   https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L1162-L1167

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
set_option autoImplicit true
@[expose] public section
public section
open P010

theorem P010.orderedPrimeClass_last (n p u v : ℕ) :
    (orderedPrimeClass n p u v).getLast? = some v := by sorry
