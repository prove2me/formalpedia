-- Prove2me | Theorems.Thm_SemigroupBetti_GenData_comp_eq_of_mem
-- name    : SemigroupBetti.GenData.comp_eq_of_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:02:32.82335+00:00
-- url     : https://prove2.me/theorems/1b1889b7-be4d-4e4b-a236-3a33c41de84e
-- title:
--   Gen Data: comp eq of mem
-- statement:
--   A component containing a factorization positive at some index of `compSupp C` is `C`.
--
--   Source: https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Partition.lean#L49-L53
-- source:
--   https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Partition.lean#L49-L53

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

theorem SemigroupBetti.GenData.comp_eq_of_mem {d : ℕ} {C : (G.nabla d).ConnectedComponent} (z : G.fiber d) {i : Fin 4}
    (hi : i ∈ G.compSupp C) (hzi : 0 < z.1 i) : (G.nabla d).connectedComponentMk z = C := by sorry
