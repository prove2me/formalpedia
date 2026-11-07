-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_indexPlacePolynomial_natDegree
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.indexPlacePolynomial_natDegree
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:35:14.580441+00:00
-- url     : https://prove2.me/theorems/577bd08c-e4da-4b84-a806-bc806924ef10
-- title:
--   Cartwright Steger: index Place Polynomial nat Degree
-- statement:
--   The Cartwright Steger construction uses the index Place Polynomial nat Degree property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Congruence/IndexSelection.lean#L318-L330
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Congruence/IndexSelection.lean#L318-L330

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_ResidueSelection
import Mathlib.GroupTheory.Coset.Card
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_IndexSelection
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open IntermediateField
open IndexSelection

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.indexPlacePolynomial_natDegree
    (P : BasePrime) (r : Rank) (level : Nat) :
    (indexPlacePolynomial P r level).natDegree =
      r.residueExponent level := by sorry
