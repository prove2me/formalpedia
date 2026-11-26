-- Prove2me | Theorems.Thm_SemigroupBetti_GenData_nu_eq_zero_iff
-- name    : SemigroupBetti.GenData.nu_eq_zero_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:28:31.560929+00:00
-- url     : https://prove2.me/theorems/a984afd0-c04c-477a-ae61-be2b8d2c381f
-- title:
--   Gen Data: nu eq zero iff
-- statement:
--   The Gen Data construction uses the nu eq zero iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Defs.lean#L146-L154
-- source:
--   https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Defs.lean#L146-L154

module
public import Mathlib
public import Definitions.Def_SemigroupBetti_Defs
set_option autoImplicit false
@[expose] public section
public section
open SemigroupBetti
open Finset
open SemigroupBetti.GenData
variable (G : GenData)

theorem SemigroupBetti.GenData.nu_eq_zero_iff {z : Fin 4 → ℕ} : G.nu z = 0 ↔ z = 0 := by sorry
