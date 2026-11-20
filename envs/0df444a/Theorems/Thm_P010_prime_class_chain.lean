-- Prove2me | Theorems.Thm_P010_prime_class_chain
-- name    : P010.prime_class_chain
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:35:54.702797+00:00
-- url     : https://prove2.me/theorems/d4638e85-90da-420f-9286-71276805d5dc
-- title:
--   P010: prime class chain
-- statement:
--   Every ordering of a class of integers sharing a prime divisor
--   is a non-coprime path. This formalizes the internal class paths.
--
--   Source: https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L237-L249
-- source:
--   https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L237-L249

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
set_option autoImplicit true
@[expose] public section
public section
open P010

theorem P010.prime_class_chain (p : ℕ) (hp : Nat.Prime p)
    (a : List ℕ) (hdiv : ∀ x ∈ a, p ∣ x) :
    NonCoprimeChain a := by sorry
