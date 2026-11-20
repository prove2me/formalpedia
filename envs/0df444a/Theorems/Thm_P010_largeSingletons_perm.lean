-- Prove2me | Theorems.Thm_P010_largeSingletons_perm
-- name    : P010.largeSingletons_perm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:42:02.648122+00:00
-- url     : https://prove2.me/theorems/699336ab-b96f-43c0-adee-3bd43c827afe
-- title:
--   P010: large Singletons perm
-- statement:
--   Large-prime singleton paths enumerate precisely the large classes.
--
--   Source: https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L2131-L2139
-- source:
--   https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L2131-L2139

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
set_option autoImplicit true
@[expose] public section
public section
open P010

theorem P010.largeSingletons_perm (n : ℕ) :
    ((largePrimes n).toList.map (fun p => [p])).flatten.Perm
      (classConcat n (largePrimes n).toList) := by sorry
