-- Prove2me | Theorems.Thm_SemigroupBetti_GenData_lemma5
-- name    : SemigroupBetti.GenData.lemma5
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:56:22.595877+00:00
-- url     : https://prove2.me/theorems/047b9509-ad1e-57d2-ba95-8dec97b1f1f1
-- title:
--   Gen Data: lemma5
-- statement:
--   **Lemma 5.** At a contributing degree without singleton-support components, `∇_d` has exactly
--   two components, and their supports form one of the partitions `01|23`, `02|13`, `03|12`.
--
--   Source: https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Partition.lean#L114-L170
-- source:
--   https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Partition.lean#L114-L170

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

theorem SemigroupBetti.GenData.lemma5 {d : ℕ} (hd : G.contributes d) (hS : ¬ G.HasSingletonComp d) :
    G.ncomp d = 2 ∧ (G.IsSplit d {0, 1} ∨ G.IsSplit d {0, 2} ∨ G.IsSplit d {0, 3}) := by sorry
