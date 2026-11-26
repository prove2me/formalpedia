-- Prove2me | Theorems.Thm_SemigroupBetti_GenData_comp_eq_critVertex
-- name    : SemigroupBetti.GenData.comp_eq_critVertex
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T03:06:45.423915+00:00
-- url     : https://prove2.me/theorems/d90b858c-8978-59cf-b2bd-cbb039ddb146
-- title:
--   Gen Data: comp eq crit Vertex
-- statement:
--   **Lemma 3.4.** At the contributing degree `cᵢ nᵢ`, a component with support `{i}` is
--   `{cᵢ eᵢ}`.
--
--   Source: https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Critical.lean#L223-L229
-- source:
--   https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Critical.lean#L223-L229

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

theorem SemigroupBetti.GenData.comp_eq_critVertex {i : Fin 4} (hd : G.contributes (G.crit i * G.n i))
    {C : (G.nabla _).ConnectedComponent} (hC : G.compSupp C = {i}) :
    C = (G.nabla _).connectedComponentMk (G.critVertex i) := by sorry
