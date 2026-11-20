-- Prove2me | Theorems.Thm_P010_leafClasses_perm
-- name    : P010.leafClasses_perm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:41:49.664449+00:00
-- url     : https://prove2.me/theorems/6e65d89e-e453-4f7e-9eb3-c331e8cfc20e
-- title:
--   P010: leaf Classes perm
-- statement:
--   The P010 construction uses the leaf Classes perm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L2115-L2121
-- source:
--   https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L2115-L2121

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
set_option autoImplicit true
@[expose] public section
public section
open P010

theorem P010.leafClasses_perm (n : ℕ) (leaves : List ℕ)
    (hleaves : ∀ p ∈ leaves, p ∈ middlePrimes n) :
    (leaves.flatMap (fun p => [p, 2 * p])).Perm
      (classConcat n leaves) := by sorry
