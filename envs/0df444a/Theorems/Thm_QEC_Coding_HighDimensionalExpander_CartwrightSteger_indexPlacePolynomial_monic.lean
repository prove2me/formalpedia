-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_indexPlacePolynomial_monic
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.indexPlacePolynomial_monic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:41:44.091877+00:00
-- url     : https://prove2.me/theorems/c966fab6-85a9-4587-aede-ded4f72a9b6a
-- title:
--   Cartwright Steger: index Place Polynomial monic
-- statement:
--   The Cartwright Steger construction uses the index Place Polynomial monic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Congruence/IndexSelection.lean#L332-L335
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Congruence/IndexSelection.lean#L332-L335

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_ResidueSelection
import Mathlib.GroupTheory.Coset.Card
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_IndexSelection
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open IntermediateField
open IndexSelection

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.indexPlacePolynomial_monic
    (P : BasePrime) (r : Rank) (level : Nat) :
    (indexPlacePolynomial P r level).Monic := by sorry
