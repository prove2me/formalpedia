-- Prove2me | Theorems.Thm_SemigroupBetti_GenData_singleton_comp_vertex
-- name    : SemigroupBetti.GenData.singleton_comp_vertex
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:56:30.78328+00:00
-- url     : https://prove2.me/theorems/cbb61513-e94c-4796-b4d3-b449613e9332
-- title:
--   Gen Data: singleton comp vertex
-- statement:
--   **Lemma 3.4 (vertex form).** At a contributing degree, every vertex of a component with
--   support `{i}` is `cᵢ eᵢ`, and the degree is `cᵢ nᵢ`.
--
--   Source: https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Critical.lean#L152-L211
-- source:
--   https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Critical.lean#L152-L211

module
public import Definitions.Def_SemigroupBetti_Fiber
public import Definitions.Def_SemigroupBetti_Critical
set_option autoImplicit false
@[expose] public section
public section
open SemigroupBetti
open Finset
open SemigroupBetti.GenData
variable (G : GenData)

theorem SemigroupBetti.GenData.singleton_comp_vertex {d : ℕ} (hd : G.contributes d) {i : Fin 4}
    {C : (G.nabla d).ConnectedComponent} (hC : G.compSupp C = {i}) (z : G.fiber d)
    (hz : (G.nabla d).connectedComponentMk z = C) :
    z.1 = Pi.single i (G.crit i) ∧ d = G.crit i * G.n i := by sorry
