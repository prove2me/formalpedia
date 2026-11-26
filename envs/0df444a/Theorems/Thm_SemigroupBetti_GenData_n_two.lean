-- Prove2me | Theorems.Thm_SemigroupBetti_GenData_n_two
-- name    : SemigroupBetti.GenData.n_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:25:27.13512+00:00
-- url     : https://prove2.me/theorems/163a544c-cc7b-40c7-8ef4-a0de5de8507d
-- title:
--   Gen Data: n two
-- statement:
--   The Gen Data construction uses the n two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Defs.lean#L89-L89
-- source:
--   https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Defs.lean#L89-L89

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

theorem SemigroupBetti.GenData.n_two : G.n 2 = G.m + G.b := by sorry

attribute [defeq] SemigroupBetti.GenData.n_two
