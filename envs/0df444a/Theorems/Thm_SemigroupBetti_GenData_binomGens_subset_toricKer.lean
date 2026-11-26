-- Prove2me | Theorems.Thm_SemigroupBetti_GenData_binomGens_subset_toricKer
-- name    : SemigroupBetti.GenData.binomGens_subset_toricKer
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:00:51.824813+00:00
-- url     : https://prove2.me/theorems/4ff06421-35c0-5dbd-89f1-c395ca4c3538
-- title:
--   Gen Data: binom Gens subset toric Ker
-- statement:
--   The Gen Data construction uses the binom Gens subset toric Ker property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Bridge.lean#L134-L144
-- source:
--   https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Bridge.lean#L134-L144

module
public import Definitions.Def_SemigroupBetti_Fiber
public import Definitions.Def_SemigroupBetti_Bridge
set_option autoImplicit false
@[expose] public section
public section
open SemigroupBetti
open Finset MvPolynomial
open SemigroupBetti.GenData
variable (G : GenData) (K : Type*) [Field K]

theorem SemigroupBetti.GenData.binomGens_subset_toricKer : (G.binomGens K : Set (MvPolynomial (Fin 4) K)) ⊆ G.toricKer K := by sorry
