-- Prove2me | Theorems.Thm_SemigroupBetti_GenData_eq_critVertex_of_reachable
-- name    : SemigroupBetti.GenData.eq_critVertex_of_reachable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:59:22.623374+00:00
-- url     : https://prove2.me/theorems/e723e432-deec-5482-8132-d4dca783a3da
-- title:
--   Gen Data: eq crit Vertex of reachable
-- statement:
--   **Lemma 3.3.** The component of `cᵢ eᵢ` is `{cᵢ eᵢ}`.
--
--   Source: https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Critical.lean#L129-L134
-- source:
--   https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Critical.lean#L129-L134

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

theorem SemigroupBetti.GenData.eq_critVertex_of_reachable (i : Fin 4) {z : G.fiber (G.crit i * G.n i)}
    (h : (G.nabla _).Reachable (G.critVertex i) z) : z = G.critVertex i := by sorry
