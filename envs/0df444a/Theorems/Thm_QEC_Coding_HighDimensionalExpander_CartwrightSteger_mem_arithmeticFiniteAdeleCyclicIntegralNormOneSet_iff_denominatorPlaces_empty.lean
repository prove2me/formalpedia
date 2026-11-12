-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_mem_arithmeticFiniteAdeleCyclicIntegralNormOneSet_iff_denominatorPlaces_empty
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.mem_arithmeticFiniteAdeleCyclicIntegralNormOneSet_iff_denominatorPlaces_empty
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T17:38:21.477222+00:00
-- url     : https://prove2.me/theorems/e73d8065-155b-4a9b-9c48-917965b454f6
-- title:
--   Cartwright Steger: mem arithmetic Finite Adele Cyclic Integral Norm One Set iff denominator Places empty
-- statement:
--   Membership in the all-integral norm-one chart is exactly the absence of
--   denominator places for the adelic unit and its inverse.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/PrasadSpecialization.lean#L1194-L1206
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/PrasadSpecialization.lean#L1194-L1206

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

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.mem_arithmeticFiniteAdeleCyclicIntegralNormOneSet_iff_denominatorPlaces_empty
    (P : BasePrime) (r : Rank)
    (u : ArithmeticFiniteAdeleCyclicNormOne P r) :
    u ∈ ArithmeticFiniteAdeleCyclicIntegralNormOneSet P r ↔
      arithmeticFiniteAdeleCyclicUnitDenominatorPlaces P r u = ∅ := by sorry
