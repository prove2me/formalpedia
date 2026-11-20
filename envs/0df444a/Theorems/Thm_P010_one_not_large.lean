-- Prove2me | Theorems.Thm_P010_one_not_large
-- name    : P010.one_not_large
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:37:24.719603+00:00
-- url     : https://prove2.me/theorems/ece948a0-9929-48cb-977f-e8850a0289a7
-- title:
--   P010: one not large
-- statement:
--   The vertex 1 is not a prime, hence not in the large-prime set.
--
--   Source: https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L573-L577
-- source:
--   https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L573-L577

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
set_option autoImplicit true
@[expose] public section
public section
open P010

theorem P010.one_not_large (n : ℕ) : 1 ∉ largePrimes n := by sorry
