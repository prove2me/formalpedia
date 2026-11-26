-- Prove2me | Theorems.Thm_SemigroupBetti_GenData_exists_full_vertex
-- name    : SemigroupBetti.GenData.exists_full_vertex
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:02:20.413366+00:00
-- url     : https://prove2.me/theorems/7fb5844c-0efb-469c-97b6-d5bd04b90ceb
-- title:
--   Gen Data: exists full vertex
-- statement:
--   **Lemma 5 (full support).** A component with support `{i, j}` contains a factorization
--   positive at both `i` and `j`.
--
--   Source: https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Partition.lean#L75-L99
-- source:
--   https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Partition.lean#L75-L99

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

theorem SemigroupBetti.GenData.exists_full_vertex {d : ℕ} {C : (G.nabla d).ConnectedComponent} {i j : Fin 4}
    (hij : i ≠ j) (hC : G.compSupp C = {i, j}) :
    ∃ z : G.fiber d, (G.nabla d).connectedComponentMk z = C ∧ 0 < z.1 i ∧ 0 < z.1 j := by sorry
