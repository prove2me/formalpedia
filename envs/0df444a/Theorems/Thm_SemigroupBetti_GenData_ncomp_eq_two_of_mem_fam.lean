-- Prove2me | Theorems.Thm_SemigroupBetti_GenData_ncomp_eq_two_of_mem_fam
-- name    : SemigroupBetti.GenData.ncomp_eq_two_of_mem_fam
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:10:50.75254+00:00
-- url     : https://prove2.me/theorems/0835d2d1-0bca-5708-b841-3a11ae38b5a0
-- title:
--   Gen Data: ncomp eq two of mem fam
-- statement:
--   The Gen Data construction uses the ncomp eq two of mem fam property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Partition.lean#L301-L303
-- source:
--   https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Partition.lean#L301-L303

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

theorem SemigroupBetti.GenData.ncomp_eq_two_of_mem_fam {K : Finset (Fin 4)} {d : ℕ} (h : d ∈ G.fam K) : G.ncomp d = 2 := by sorry
