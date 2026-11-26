-- Prove2me | Theorems.Thm_SemigroupBetti_GenData_exists_not_reachable
-- name    : SemigroupBetti.GenData.exists_not_reachable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:29:57.276212+00:00
-- url     : https://prove2.me/theorems/05fff829-1b82-42ca-b89e-0ccf077ff790
-- title:
--   Gen Data: exists not reachable
-- statement:
--   The Gen Data construction uses the exists not reachable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Fiber.lean#L103-L108
-- source:
--   https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Fiber.lean#L103-L108

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

theorem SemigroupBetti.GenData.exists_not_reachable {d : ℕ} (h : 2 ≤ G.ncomp d) :
    ∃ z y : G.fiber d, ¬ (G.nabla d).Reachable z y := by sorry
