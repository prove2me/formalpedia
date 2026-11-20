-- Prove2me | Theorems.Thm_P010_threeEvenUnit_none_perm
-- name    : P010.threeEvenUnit_none_perm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:41:23.347184+00:00
-- url     : https://prove2.me/theorems/15ca2ecc-0a98-47c0-ae9e-50cf7948e5bf
-- title:
--   P010: three Even Unit none perm
-- statement:
--   The prime-3 unit without an unmatched intermediate class
--   enumerates just its own class.
--
--   Source: https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L1929-L1933
-- source:
--   https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L1929-L1933

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
set_option autoImplicit true
@[expose] public section
public section
open P010

theorem P010.threeEvenUnit_none_perm (n : ℕ) (hn : 12 ≤ n) :
    (threeEvenUnit n none).Perm (classConcat n [3]) := by sorry
