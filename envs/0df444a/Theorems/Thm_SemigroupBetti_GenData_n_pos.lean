-- Prove2me | Theorems.Thm_SemigroupBetti_GenData_n_pos
-- name    : SemigroupBetti.GenData.n_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:26:37.598565+00:00
-- url     : https://prove2.me/theorems/ba3f3892-f7f6-4bb5-9098-3b4119c53530
-- title:
--   Gen Data: n pos
-- statement:
--   The Gen Data construction uses the n pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Defs.lean#L113-L113
-- source:
--   https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Defs.lean#L113-L113

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

theorem SemigroupBetti.GenData.n_pos (i : Fin 4) : 0 < G.n i := by sorry
