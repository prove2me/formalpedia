-- Prove2me | Theorems.Thm_SemigroupBetti_GenData_n_eq_normalized
-- name    : SemigroupBetti.GenData.n_eq_normalized
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:29:21.671703+00:00
-- url     : https://prove2.me/theorems/4e33f86a-9db2-4284-9bd0-94e81ecce7ef
-- title:
--   Gen Data: n eq normalized
-- statement:
--   The Gen Data construction uses the n eq normalized property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Defs.lean#L200-L201
-- source:
--   https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Defs.lean#L200-L201

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

theorem SemigroupBetti.GenData.n_eq_normalized : G.n = ![G.m, G.m + G.g * G.A, G.m + G.g * G.B, G.m + G.g * G.W] := by sorry
