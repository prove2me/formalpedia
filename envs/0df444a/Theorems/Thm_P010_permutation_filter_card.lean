-- Prove2me | Theorems.Thm_P010_permutation_filter_card
-- name    : P010.permutation_filter_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:37:58.631992+00:00
-- url     : https://prove2.me/theorems/2ec0028e-0000-4afa-880f-444732ad52a7
-- title:
--   P010: permutation filter card
-- statement:
--   A finite subset of [1,n] occurs with its exact cardinality in
--   any permutation of [1,n].
--
--   Source: https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L636-L656
-- source:
--   https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L636-L656

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
set_option autoImplicit true
@[expose] public section
public section
open P010

theorem P010.permutation_filter_card (n : ℕ) (a : List ℕ)
    (ha : IsPermutation n a) (s : Finset ℕ)
    (hs : ∀ x ∈ s, 1 ≤ x ∧ x ≤ n) :
    (a.filter (fun x => decide (x ∈ s))).length = s.card := by sorry
