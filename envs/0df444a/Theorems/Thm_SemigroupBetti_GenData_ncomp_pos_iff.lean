-- Prove2me | Theorems.Thm_SemigroupBetti_GenData_ncomp_pos_iff
-- name    : SemigroupBetti.GenData.ncomp_pos_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:32:09.012801+00:00
-- url     : https://prove2.me/theorems/6cfd9702-d2c6-5ba5-841e-ce92271243ca
-- title:
--   Gen Data: ncomp pos iff
-- statement:
--   The Gen Data construction uses the ncomp pos iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Fiber.lean#L117-L118
-- source:
--   https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Fiber.lean#L117-L118

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

theorem SemigroupBetti.GenData.ncomp_pos_iff {d : ℕ} : 0 < G.ncomp d ↔ (G.fiber d).Nonempty := by sorry
