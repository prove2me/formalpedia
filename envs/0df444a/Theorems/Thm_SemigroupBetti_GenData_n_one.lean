-- Prove2me | Theorems.Thm_SemigroupBetti_GenData_n_one
-- name    : SemigroupBetti.GenData.n_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:25:19.413385+00:00
-- url     : https://prove2.me/theorems/0c6f2ec6-cdac-5ba5-a8c6-764f979b9262
-- title:
--   Gen Data: n one
-- statement:
--   The Gen Data construction uses the n one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Defs.lean#L88-L88
-- source:
--   https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Defs.lean#L88-L88

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

theorem SemigroupBetti.GenData.n_one : G.n 1 = G.m + G.a := by sorry

attribute [defeq] SemigroupBetti.GenData.n_one
