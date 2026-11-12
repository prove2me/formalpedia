-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cyclicAlgebraNormOneDenominatorPlaces_eq_empty_iff
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.cyclicAlgebraNormOneDenominatorPlaces_eq_empty_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T18:09:13.001521+00:00
-- url     : https://prove2.me/theorems/32f0cb8e-ad3c-40ca-98f7-9a75a9a79b39
-- title:
--   Cartwright Steger: cyclic Algebra Norm One Denominator Places eq empty iff
-- statement:
--   The Cartwright Steger construction uses the cyclic Algebra Norm One Denominator Places eq empty iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/PrasadSpecialization.lean#L1222-L1228
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/PrasadSpecialization.lean#L1222-L1228

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_IntrinsicStrongApproximation
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
import Mathlib.RingTheory.LaurentSeries
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.RingTheory.Flat.Equalizer
import Mathlib.Topology.Algebra.Group.Matrix
import Mathlib.Topology.Algebra.IsOpenUnits
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_PrasadSpecialization
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped TensorProduct
open scoped commutatorElement
open Topology

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.cyclicAlgebraNormOneDenominatorPlaces_eq_empty_iff
    (P : BasePrime) (r : Rank) (u : CyclicAlgebraNormOne P r) :
    cyclicAlgebraNormOneDenominatorPlaces P r u = ∅ ↔
      cyclicAlgebraNormOneToArithmeticFiniteAdeleNormOne P r u ∈
        ArithmeticFiniteAdeleCyclicIntegralNormOneSet P r := by sorry
