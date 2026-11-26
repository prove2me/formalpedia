-- Prove2me | Theorems.Thm_SemigroupBetti_GenData_coord_le_of_contributes
-- name    : SemigroupBetti.GenData.coord_le_of_contributes
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:31:45.25069+00:00
-- url     : https://prove2.me/theorems/e084baae-cec3-4b50-874a-88cdf34aae7a
-- title:
--   Gen Data: coord le of contributes
-- statement:
--   **Lemma 0A.** At a contributing degree every coordinate of every factorization is at
--   most `N = n₃`.
--
--   Source: https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Fiber.lean#L215-L220
-- source:
--   https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Fiber.lean#L215-L220

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

theorem SemigroupBetti.GenData.coord_le_of_contributes {d : ℕ} (h : G.contributes d) (z : G.fiber d) (i : Fin 4) :
    z.1 i ≤ G.n 3 := by sorry
