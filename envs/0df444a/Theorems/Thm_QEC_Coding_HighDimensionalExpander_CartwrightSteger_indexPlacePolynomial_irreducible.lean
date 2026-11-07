-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_indexPlacePolynomial_irreducible
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.indexPlacePolynomial_irreducible
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:41:46.016876+00:00
-- url     : https://prove2.me/theorems/e554e0de-793b-4e81-b703-087578bdb6bd
-- title:
--   Cartwright Steger: index Place Polynomial irreducible
-- statement:
--   The Cartwright Steger construction uses the index Place Polynomial irreducible property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Congruence/IndexSelection.lean#L337-L340
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Congruence/IndexSelection.lean#L337-L340

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_ResidueSelection
import Mathlib.GroupTheory.Coset.Card
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_IndexSelection
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open IntermediateField
open IndexSelection

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.indexPlacePolynomial_irreducible
    (P : BasePrime) (r : Rank) (level : Nat) :
    Irreducible (indexPlacePolynomial P r level) := by sorry
