-- Prove2me | Theorems.Thm_P010_classConcat_all_primes
-- name    : P010.classConcat_all_primes
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:41:33.225224+00:00
-- url     : https://prove2.me/theorems/c2d881f2-4a8d-4acc-8c54-640443bd108c
-- title:
--   P010: class Concat all primes
-- statement:
--   Concatenating all largest-prime-factor classes yields precisely
--   the integers 2,...,n, without repetition.
--
--   Source: https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L1871-L1879
-- source:
--   https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L1871-L1879

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
set_option autoImplicit true
@[expose] public section
public section
open P010

theorem P010.classConcat_all_primes (n : ℕ) :
    (classConcat n n.primesLE.toList).Perm
      (Finset.Icc 2 n).toList := by sorry
