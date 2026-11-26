-- Prove2me | Theorems.Thm_SemigroupBetti_GenData_n_mono
-- name    : SemigroupBetti.GenData.n_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:26:08.464103+00:00
-- url     : https://prove2.me/theorems/fad5b826-35f4-4a0b-b97c-cf6a59db8ba5
-- title:
--   Gen Data: n mono
-- statement:
--   The Gen Data construction uses the n mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Defs.lean#L108-L108
-- source:
--   https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Defs.lean#L108-L108

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

theorem SemigroupBetti.GenData.n_mono : Monotone G.n := by sorry
