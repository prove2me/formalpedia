-- Prove2me | Theorems.Thm_SemigroupBetti_GenData_n_three
-- name    : SemigroupBetti.GenData.n_three
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:25:23.788548+00:00
-- url     : https://prove2.me/theorems/51c6899d-2278-5d17-8342-7b21f5d3b121
-- title:
--   Gen Data: n three
-- statement:
--   The Gen Data construction uses the n three property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Defs.lean#L90-L90
-- source:
--   https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Defs.lean#L90-L90

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

theorem SemigroupBetti.GenData.n_three : G.n 3 = G.m + G.w := by sorry

attribute [defeq] SemigroupBetti.GenData.n_three
