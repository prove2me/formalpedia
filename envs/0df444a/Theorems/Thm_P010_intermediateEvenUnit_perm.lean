-- Prove2me | Theorems.Thm_P010_intermediateEvenUnit_perm
-- name    : P010.intermediateEvenUnit_perm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:41:13.836164+00:00
-- url     : https://prove2.me/theorems/f04115e0-f94e-4eac-9951-62d79c4112ff
-- title:
--   P010: intermediate Even Unit perm
-- statement:
--   A paired intermediate unit enumerates both of its classes.
--
--   Source: https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L1911-L1925
-- source:
--   https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L1911-L1925

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
set_option autoImplicit true
@[expose] public section
public section
open P010

theorem P010.intermediateEvenUnit_perm (n p q : ℕ) (hn : 12 ≤ n)
    (hp : p ∈ intermediatePrimes n)
    (hq : q ∈ intermediatePrimes n) :
    (intermediateEvenUnit n (p, q)).Perm (classConcat n [p, q]) := by sorry
