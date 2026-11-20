-- Prove2me | Theorems.Thm_P010_smallUnits_perm
-- name    : P010.smallUnits_perm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:41:56.293371+00:00
-- url     : https://prove2.me/theorems/74eee184-08fa-4c9f-b939-5d3384d4eb61
-- title:
--   P010: small Units perm
-- statement:
--   Small-unit concatenation enumerates exactly the classes
--   indexed by the prescribed small-prime list.
--
--   Source: https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L1975-L1983
-- source:
--   https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L1975-L1983

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
set_option autoImplicit true
@[expose] public section
public section
open P010

theorem P010.smallUnits_perm (n : ℕ) (small : List ℕ)
    (hsmall : ∀ p ∈ small, Nat.Prime p ∧ 4 * p ≤ n) :
    (small.map (smallEvenUnit n)).flatten.Perm (classConcat n small) := by sorry
