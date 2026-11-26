-- Prove2me | Theorems.Thm_SemigroupBetti_GenData_reachable_of_coord_gt
-- name    : SemigroupBetti.GenData.reachable_of_coord_gt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:31:07.523203+00:00
-- url     : https://prove2.me/theorems/c73269b7-3466-4343-b4c0-b80a76d60224
-- title:
--   Gen Data: reachable of coord gt
-- statement:
--   Core of Lemma 0A: a factorization with a coordinate exceeding `N = n₃` is connected to
--   every other factorization of the same degree.
--
--   Source: https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Fiber.lean#L185-L211
-- source:
--   https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Fiber.lean#L185-L211

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

theorem SemigroupBetti.GenData.reachable_of_coord_gt {d : ℕ} (z y : G.fiber d) {i : Fin 4} (hzi : G.n 3 < z.1 i) :
    (G.nabla d).Reachable z y := by sorry
