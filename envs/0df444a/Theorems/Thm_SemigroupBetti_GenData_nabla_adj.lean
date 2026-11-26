-- Prove2me | Theorems.Thm_SemigroupBetti_GenData_nabla_adj
-- name    : SemigroupBetti.GenData.nabla_adj
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:32:00.652529+00:00
-- url     : https://prove2.me/theorems/f59d007e-177d-402c-9000-5cc50f639a41
-- title:
--   Gen Data: nabla adj
-- statement:
--   The Gen Data construction uses the nabla adj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Fiber.lean#L55-L56
-- source:
--   https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Fiber.lean#L55-L56

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

theorem SemigroupBetti.GenData.nabla_adj {d : ℕ} {z z' : G.fiber d} :
    (G.nabla d).Adj z z' ↔ z ≠ z' ∧ SharesVar z.1 z'.1 := by sorry
