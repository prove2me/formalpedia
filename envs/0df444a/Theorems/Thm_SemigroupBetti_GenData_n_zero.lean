-- Prove2me | Theorems.Thm_SemigroupBetti_GenData_n_zero
-- name    : SemigroupBetti.GenData.n_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:25:39.314165+00:00
-- url     : https://prove2.me/theorems/3c10e750-8185-4854-a3d6-840c5fda9a3f
-- title:
--   Gen Data: n zero
-- statement:
--   The Gen Data construction uses the n zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Defs.lean#L87-L87
-- source:
--   https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Defs.lean#L87-L87

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

theorem SemigroupBetti.GenData.n_zero : G.n 0 = G.m := by sorry

attribute [defeq] SemigroupBetti.GenData.n_zero
