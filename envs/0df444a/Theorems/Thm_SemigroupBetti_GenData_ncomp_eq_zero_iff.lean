-- Prove2me | Theorems.Thm_SemigroupBetti_GenData_ncomp_eq_zero_iff
-- name    : SemigroupBetti.GenData.ncomp_eq_zero_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:30:56.613925+00:00
-- url     : https://prove2.me/theorems/816430e4-f5d9-4312-ab1c-499d9f3e5e5f
-- title:
--   Gen Data: ncomp eq zero iff
-- statement:
--   The Gen Data construction uses the ncomp eq zero iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Fiber.lean#L110-L115
-- source:
--   https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Fiber.lean#L110-L115

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

theorem SemigroupBetti.GenData.ncomp_eq_zero_iff {d : ℕ} : G.ncomp d = 0 ↔ G.fiber d = ∅ := by sorry
