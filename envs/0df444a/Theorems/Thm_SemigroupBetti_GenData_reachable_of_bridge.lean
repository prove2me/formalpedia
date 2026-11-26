-- Prove2me | Theorems.Thm_SemigroupBetti_GenData_reachable_of_bridge
-- name    : SemigroupBetti.GenData.reachable_of_bridge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:30:03.799174+00:00
-- url     : https://prove2.me/theorems/acd376e3-799f-5cda-a934-951165032913
-- title:
--   Gen Data: reachable of bridge
-- statement:
--   **Lemma 2.4.** A factorization `b` of `d` sharing a variable with `z` and with `y` puts
--   `z` and `y` in the same component.
--
--   Source: https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Fiber.lean#L167-L170
-- source:
--   https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Fiber.lean#L167-L170

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

theorem SemigroupBetti.GenData.reachable_of_bridge {d : ℕ} {z y : G.fiber d} (b : Fin 4 → ℕ) (hb : G.nu b = d)
    (hz : SharesVar b z.1) (hy : SharesVar b y.1) : (G.nabla d).Reachable z y := by sorry
