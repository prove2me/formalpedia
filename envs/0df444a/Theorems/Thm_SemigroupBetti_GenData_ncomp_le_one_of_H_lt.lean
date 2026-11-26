-- Prove2me | Theorems.Thm_SemigroupBetti_GenData_ncomp_le_one_of_H_lt
-- name    : SemigroupBetti.GenData.ncomp_le_one_of_H_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:31:23.764447+00:00
-- url     : https://prove2.me/theorems/6e443566-66ac-5645-a5d2-be24491bcf96
-- title:
--   Gen Data: ncomp le one of H lt
-- statement:
--   **Lemma 0A (cutoff form).** Above `H`, `∇_d` has at most one component.
--
--   Source: https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Fiber.lean#L229-L233
-- source:
--   https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Fiber.lean#L229-L233

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

theorem SemigroupBetti.GenData.ncomp_le_one_of_H_lt {d : ℕ} (h : G.H < d) : G.ncomp d ≤ 1 := by sorry
