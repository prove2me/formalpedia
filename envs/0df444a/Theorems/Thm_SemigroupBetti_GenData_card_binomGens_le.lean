-- Prove2me | Theorems.Thm_SemigroupBetti_GenData_card_binomGens_le
-- name    : SemigroupBetti.GenData.card_binomGens_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:00:44.477461+00:00
-- url     : https://prove2.me/theorems/a716658c-d60e-5f97-9cea-378891b6da5b
-- title:
--   Gen Data: card binom Gens le
-- statement:
--   The Gen Data construction uses the card binom Gens le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Bridge.lean#L130-L132
-- source:
--   https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Bridge.lean#L130-L132

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

theorem SemigroupBetti.GenData.card_binomGens_le : #(G.binomGens K) ≤ G.beta1 := by sorry
