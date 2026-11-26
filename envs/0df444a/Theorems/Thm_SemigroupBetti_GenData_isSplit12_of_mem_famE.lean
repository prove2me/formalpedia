-- Prove2me | Theorems.Thm_SemigroupBetti_GenData_isSplit12_of_mem_famE
-- name    : SemigroupBetti.GenData.isSplit12_of_mem_famE
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:55:47.310424+00:00
-- url     : https://prove2.me/theorems/cb0f9416-2db1-48c3-9899-5ebf43d59dfc
-- title:
--   Gen Data: is Split12 of mem fam E
-- statement:
--   The Gen Data construction uses the is Split12 of mem fam E property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Antichain.lean#L195-L197
-- source:
--   https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Antichain.lean#L195-L197

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

theorem SemigroupBetti.GenData.isSplit12_of_mem_famE {d : ℕ} (h : d ∈ G.famE) : G.IsSplit d {1, 2} := by sorry
