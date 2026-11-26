-- Prove2me | Theorems.Thm_SemigroupBetti_GenData_nu_pos_of_pos
-- name    : SemigroupBetti.GenData.nu_pos_of_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:28:40.64637+00:00
-- url     : https://prove2.me/theorems/010f631d-262c-4a92-a2f9-7355e26761cb
-- title:
--   Gen Data: nu pos of pos
-- statement:
--   The Gen Data construction uses the nu pos of pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Defs.lean#L156-L157
-- source:
--   https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Defs.lean#L156-L157

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

theorem SemigroupBetti.GenData.nu_pos_of_pos {z : Fin 4 → ℕ} {i : Fin 4} (h : 0 < z i) : 0 < G.nu z := by sorry
