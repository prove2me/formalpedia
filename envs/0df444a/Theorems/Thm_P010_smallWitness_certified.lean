-- Prove2me | Theorems.Thm_P010_smallWitness_certified
-- name    : P010.smallWitness_certified
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:37:02.63389+00:00
-- url     : https://prove2.me/theorems/aa2ce3d6-5900-49e1-b8e5-a6f44e5a7af9
-- title:
--   P010: small Witness certified
-- statement:
--   The P010 construction uses the small Witness certified property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L193-L197
-- source:
--   https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L193-L197

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
set_option autoImplicit true
@[expose] public section
public section
open P010

theorem P010.smallWitness_certified (n : ℕ) (hnpos : 1 ≤ n) (hnmax : n ≤ 11) :
    IsPermutation n (smallWitness n) ∧
      adjacentCount (smallWitness n) =
        (if n ≤ 3 then n - 1 else target n) := by sorry
