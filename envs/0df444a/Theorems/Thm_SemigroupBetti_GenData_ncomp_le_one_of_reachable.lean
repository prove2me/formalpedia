-- Prove2me | Theorems.Thm_SemigroupBetti_GenData_ncomp_le_one_of_reachable
-- name    : SemigroupBetti.GenData.ncomp_le_one_of_reachable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:30:46.833119+00:00
-- url     : https://prove2.me/theorems/72a626a9-5a4e-424a-86ad-fdce8adeb63b
-- title:
--   Gen Data: ncomp le one of reachable
-- statement:
--   The Gen Data construction uses the ncomp le one of reachable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Fiber.lean#L96-L101
-- source:
--   https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Fiber.lean#L96-L101

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

theorem SemigroupBetti.GenData.ncomp_le_one_of_reachable {d : ℕ} (h : ∀ z y : G.fiber d, (G.nabla d).Reachable z y) :
    G.ncomp d ≤ 1 := by sorry
