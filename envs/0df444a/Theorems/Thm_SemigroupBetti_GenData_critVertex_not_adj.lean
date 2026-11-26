-- Prove2me | Theorems.Thm_SemigroupBetti_GenData_critVertex_not_adj
-- name    : SemigroupBetti.GenData.critVertex_not_adj
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:59:22.340491+00:00
-- url     : https://prove2.me/theorems/718769d1-a754-5ac2-881d-f23c2af62bea
-- title:
--   Gen Data: crit Vertex not adj
-- statement:
--   **Lemma 3.3.** `cᵢ eᵢ` is isolated in `∇_{cᵢ nᵢ}`.
--
--   Source: https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Critical.lean#L118-L126
-- source:
--   https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Critical.lean#L118-L126

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

theorem SemigroupBetti.GenData.critVertex_not_adj (i : Fin 4) (z : G.fiber (G.crit i * G.n i)) :
    ¬ (G.nabla _).Adj (G.critVertex i) z := by sorry
