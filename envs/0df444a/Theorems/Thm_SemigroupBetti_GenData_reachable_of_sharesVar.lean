-- Prove2me | Theorems.Thm_SemigroupBetti_GenData_reachable_of_sharesVar
-- name    : SemigroupBetti.GenData.reachable_of_sharesVar
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:29:57.446139+00:00
-- url     : https://prove2.me/theorems/5d8788d0-acde-4d44-b2db-b6f99d953eed
-- title:
--   Gen Data: reachable of shares Var
-- statement:
--   The Gen Data construction uses the reachable of shares Var property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Fiber.lean#L90-L94
-- source:
--   https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Fiber.lean#L90-L94

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

theorem SemigroupBetti.GenData.reachable_of_sharesVar {d : ℕ} {z y : G.fiber d} (h : SharesVar z.1 y.1) :
    (G.nabla d).Reachable z y := by sorry
