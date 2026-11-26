-- Prove2me | Theorems.Thm_SemigroupBetti_GenData_sel_spec
-- name    : SemigroupBetti.GenData.sel_spec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:02:20.313709+00:00
-- url     : https://prove2.me/theorems/026099e2-326d-4b4b-b3b7-4ae1f725ad35
-- title:
--   Gen Data: sel spec
-- statement:
--   The Gen Data construction uses the sel spec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Partition.lean#L208-L211
-- source:
--   https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Partition.lean#L208-L211

module
public import Definitions.Def_SemigroupBetti_Critical
public import Definitions.Def_SemigroupBetti_Partition
set_option autoImplicit false
@[expose] public section
public section
open SemigroupBetti
open Finset
open SemigroupBetti.GenData
variable (G : GenData)

theorem SemigroupBetti.GenData.sel_spec {d : ℕ} {K : Finset (Fin 4)} (h : ∃ z : Fin 4 → ℕ, G.nu z = d ∧ supp z = K) :
    G.nu (G.sel d K) = d ∧ supp (G.sel d K) = K := by sorry
