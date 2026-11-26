-- Prove2me | Theorems.Thm_SemigroupBetti_GenData_mem_fiber
-- name    : SemigroupBetti.GenData.mem_fiber
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:29:55.170981+00:00
-- url     : https://prove2.me/theorems/814ed4f6-ded3-41d4-a541-9cbf66d4c2dd
-- title:
--   Gen Data: mem fiber
-- statement:
--   The Gen Data construction uses the mem fiber property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Fiber.lean#L37-L39
-- source:
--   https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Fiber.lean#L37-L39

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

theorem SemigroupBetti.GenData.mem_fiber {d : ℕ} {z : Fin 4 → ℕ} : z ∈ G.fiber d ↔ G.nu z = d := by sorry
