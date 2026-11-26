-- Prove2me | Theorems.Thm_SemigroupBetti_GenData_toricKer_le_span
-- name    : SemigroupBetti.GenData.toricKer_le_span
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:01:25.068531+00:00
-- url     : https://prove2.me/theorems/24fcc8bb-289f-5e5a-b058-3a1b453fe251
-- title:
--   Gen Data: toric Ker le span
-- statement:
--   The Gen Data construction uses the toric Ker le span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Bridge.lean#L253-L272
-- source:
--   https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Bridge.lean#L253-L272

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

theorem SemigroupBetti.GenData.toricKer_le_span : G.toricKer K ≤ Ideal.span (G.binomGens K : Set _) := by sorry
