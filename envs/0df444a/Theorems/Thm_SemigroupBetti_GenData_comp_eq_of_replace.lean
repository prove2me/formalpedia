-- Prove2me | Theorems.Thm_SemigroupBetti_GenData_comp_eq_of_replace
-- name    : SemigroupBetti.GenData.comp_eq_of_replace
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:32:58.609883+00:00
-- url     : https://prove2.me/theorems/0334591b-4202-4d39-8b98-1fd8be1ffc66
-- title:
--   Gen Data: comp eq of replace
-- statement:
--   **Lemma 2.4 (as stated).** With `u ≤ x`, `ν(u) = ν(v)`, `ν(x) = d`, if `b = x - u + v`
--   shares variables with vertices of two components then the components coincide.
--
--   Source: https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Fiber.lean#L174-L179
-- source:
--   https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Fiber.lean#L174-L179

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

theorem SemigroupBetti.GenData.comp_eq_of_replace {d : ℕ} {u v x : Fin 4 → ℕ} (hux : u ≤ x) (huv : G.nu u = G.nu v)
    (hx : G.nu x = d) {z y : G.fiber d} (hz : SharesVar (x - u + v) z.1)
    (hy : SharesVar (x - u + v) y.1) :
    (G.nabla d).connectedComponentMk z = (G.nabla d).connectedComponentMk y := by sorry
