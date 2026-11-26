-- Prove2me | Theorems.Thm_SemigroupBetti_GenData_mem_singletonDegrees
-- name    : SemigroupBetti.GenData.mem_singletonDegrees
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:53:37.949586+00:00
-- url     : https://prove2.me/theorems/e77c043f-816c-5fb4-8e19-0a413ae16ae2
-- title:
--   Gen Data: mem singleton Degrees
-- statement:
--   The Gen Data construction uses the mem singleton Degrees property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Critical.lean#L252-L255
-- source:
--   https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Critical.lean#L252-L255

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

theorem SemigroupBetti.GenData.mem_singletonDegrees {d : ℕ} :
    d ∈ G.singletonDegrees ↔ d ≤ G.H ∧ G.contributes d ∧ G.HasSingletonComp d := by sorry
