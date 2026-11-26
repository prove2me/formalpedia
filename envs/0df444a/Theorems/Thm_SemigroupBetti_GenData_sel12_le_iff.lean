-- Prove2me | Theorems.Thm_SemigroupBetti_GenData_sel12_le_iff
-- name    : SemigroupBetti.GenData.sel12_le_iff
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T02:58:22.528985+00:00
-- url     : https://prove2.me/theorems/210f768c-66aa-5ee7-af9c-a633422b836b
-- title:
--   Gen Data: sel12 le iff
-- statement:
--   The Gen Data construction uses the sel12 le iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Antichain.lean#L222-L235
-- source:
--   https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Antichain.lean#L222-L235

module
public import Definitions.Def_SemigroupBetti_Identities
public import Definitions.Def_SemigroupBetti_Antichain
set_option autoImplicit false
@[expose] public section
public section
open SemigroupBetti
open Finset
open SemigroupBetti.GenData
variable (G : GenData)

theorem SemigroupBetti.GenData.sel12_le_iff {d d' : ℕ} (hd : d ∈ G.famE) (hd' : d' ∈ G.famE) :
    G.sel d {1, 2} ≤ G.sel d' {1, 2} ↔
      G.sel d {1, 2} 1 ≤ G.sel d' {1, 2} 1 ∧ G.sel d {1, 2} 2 ≤ G.sel d' {1, 2} 2 := by sorry
