-- Prove2me | Theorems.Thm_SemigroupBetti_GenData_compSupp_critVertex
-- name    : SemigroupBetti.GenData.compSupp_critVertex
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:59:47.420276+00:00
-- url     : https://prove2.me/theorems/ad925cbc-993d-519b-b693-ab80ff4723e2
-- title:
--   Gen Data: comp Supp crit Vertex
-- statement:
--   **Lemma 3.3.** The component `{cᵢ eᵢ}` has support `{i}`.
--
--   Source: https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Critical.lean#L137-L148
-- source:
--   https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Critical.lean#L137-L148

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

theorem SemigroupBetti.GenData.compSupp_critVertex (i : Fin 4) :
    G.compSupp ((G.nabla _).connectedComponentMk (G.critVertex i)) = {i} := by sorry
