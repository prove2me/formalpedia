-- Prove2me | Theorems.Thm_SemigroupBetti_GenData_mem_compSupp
-- name    : SemigroupBetti.GenData.mem_compSupp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:29:42.368086+00:00
-- url     : https://prove2.me/theorems/2f2d759d-df0d-5a14-a05f-b8a232e1d674
-- title:
--   Gen Data: mem comp Supp
-- statement:
--   The Gen Data construction uses the mem comp Supp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Fiber.lean#L79-L82
-- source:
--   https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Fiber.lean#L79-L82

module
public import Definitions.Def_SemigroupBetti_Defs
public import Definitions.Def_SemigroupBetti_Fiber
set_option autoImplicit false
@[expose] public section
public section
open SemigroupBetti
open Finset
open SemigroupBetti.GenData
variable (G : GenData)

theorem SemigroupBetti.GenData.mem_compSupp {d : ℕ} {C : (G.nabla d).ConnectedComponent} {i : Fin 4} :
    i ∈ G.compSupp C ↔ ∃ z : G.fiber d, (G.nabla d).connectedComponentMk z = C ∧ 0 < z.1 i := by sorry
