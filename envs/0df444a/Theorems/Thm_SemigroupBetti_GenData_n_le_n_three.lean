-- Prove2me | Theorems.Thm_SemigroupBetti_GenData_n_le_n_three
-- name    : SemigroupBetti.GenData.n_le_n_three
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:28:03.669578+00:00
-- url     : https://prove2.me/theorems/3d8bd07c-4a37-4a46-b847-ff2068af28ec
-- title:
--   Gen Data: n le n three
-- statement:
--   The Gen Data construction uses the n le n three property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Defs.lean#L115-L115
-- source:
--   https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Defs.lean#L115-L115

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

theorem SemigroupBetti.GenData.n_le_n_three (i : Fin 4) : G.n i ≤ G.n 3 := by sorry
