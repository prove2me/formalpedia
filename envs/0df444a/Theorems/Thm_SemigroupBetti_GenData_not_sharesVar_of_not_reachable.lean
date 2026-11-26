-- Prove2me | Theorems.Thm_SemigroupBetti_GenData_not_sharesVar_of_not_reachable
-- name    : SemigroupBetti.GenData.not_sharesVar_of_not_reachable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:32:17.717521+00:00
-- url     : https://prove2.me/theorems/de28d0a3-8e1c-5272-b7fe-23d7c58e0971
-- title:
--   Gen Data: not shares Var of not reachable
-- statement:
--   **Lemma 2.1 (vertex form).** Vertices in different components share no variable.
--
--   Source: https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Fiber.lean#L136-L138
-- source:
--   https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Fiber.lean#L136-L138

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

theorem SemigroupBetti.GenData.not_sharesVar_of_not_reachable {d : ℕ} {z y : G.fiber d}
    (h : ¬ (G.nabla d).Reachable z y) : ¬ SharesVar z.1 y.1 := by sorry
