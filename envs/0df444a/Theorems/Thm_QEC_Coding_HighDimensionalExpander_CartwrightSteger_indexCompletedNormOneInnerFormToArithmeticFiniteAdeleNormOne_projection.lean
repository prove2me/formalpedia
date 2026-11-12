-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_indexCompletedNormOneInnerFormToArithmeticFiniteAdeleNormOne_projection
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.indexCompletedNormOneInnerFormToArithmeticFiniteAdeleNormOne_projection
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T17:54:26.007208+00:00
-- url     : https://prove2.me/theorems/9648c60b-d6e4-4734-bc4c-04934822bd8b
-- title:
--   Cartwright Steger: index Completed Norm One Inner Form To Arithmetic Finite Adele Norm One projection
-- statement:
--   Selected-place localization of the integral adelic lift recovers the
--   original completed special-linear point after the canonical Laurent
--   embedding.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/PrasadSpecialization.lean#L6689-L6714
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/PrasadSpecialization.lean#L6689-L6714

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

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.indexCompletedNormOneInnerFormToArithmeticFiniteAdeleNormOne_projection
    (P : BasePrime) (r : Rank) (level : Nat)
    (s : IndexCompletedNormOneInnerForm P r level) :
    indexLocalCyclicAlgebraNormOneEquivSL P r level
        (arithmeticFiniteAdeleNormOneToIndexLocalNormOne P r level
          (indexCompletedNormOneInnerFormToArithmeticFiniteAdeleNormOne
            P r level s)) =
      indexCompletedNormOneInnerFormToIndexLocal P r level s := by sorry
