-- Prove2me | Theorems.Thm_P010_orderedPrimeClass_nodup
-- name    : P010.orderedPrimeClass_nodup
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:39:00.248054+00:00
-- url     : https://prove2.me/theorems/69150541-de85-460b-8ae1-643e763c5323
-- title:
--   P010: ordered Prime Class nodup
-- statement:
--   The ordering has no repeated vertex when endpoints are distinct.
--
--   Source: https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L1133-L1145
-- source:
--   https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L1133-L1145

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
set_option autoImplicit true
@[expose] public section
public section
open P010

theorem P010.orderedPrimeClass_nodup (n p u v : ℕ) (huv : u ≠ v) :
    (orderedPrimeClass n p u v).Nodup := by sorry
