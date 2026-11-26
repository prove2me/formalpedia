-- Prove2me | Theorems.Thm_SemigroupBetti_GenData_mem_fam
-- name    : SemigroupBetti.GenData.mem_fam
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:54:33.534388+00:00
-- url     : https://prove2.me/theorems/ebb85976-c210-4547-8863-c51ab27505e4
-- title:
--   Gen Data: mem fam
-- statement:
--   The Gen Data construction uses the mem fam property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Partition.lean#L188-L191
-- source:
--   https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Partition.lean#L188-L191

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

theorem SemigroupBetti.GenData.mem_fam {K : Finset (Fin 4)} {d : ℕ} :
    d ∈ G.fam K ↔ d ≤ G.H ∧ G.contributes d ∧ ¬ G.HasSingletonComp d ∧ G.IsSplit d K := by sorry
