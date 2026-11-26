-- Prove2me | Theorems.Thm_SemigroupBetti_GenData_degree_eq_of_singleton_comp
-- name    : SemigroupBetti.GenData.degree_eq_of_singleton_comp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:00:10.048457+00:00
-- url     : https://prove2.me/theorems/c090ad36-d372-4329-8229-644267120ca7
-- title:
--   Gen Data: degree eq of singleton comp
-- statement:
--   **Lemma 3.4.** At a contributing degree, a component with support `{i}` lives in degree
--   `cᵢ nᵢ`.
--
--   Source: https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Critical.lean#L215-L219
-- source:
--   https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Critical.lean#L215-L219

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

theorem SemigroupBetti.GenData.degree_eq_of_singleton_comp {d : ℕ} (hd : G.contributes d) {i : Fin 4}
    {C : (G.nabla d).ConnectedComponent} (hC : G.compSupp C = {i}) :
    d = G.crit i * G.n i := by sorry
