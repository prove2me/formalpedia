-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cyclicAlgebraNormOneToSplittingSL_toGL
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.cyclicAlgebraNormOneToSplittingSL_toGL
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T17:35:47.177652+00:00
-- url     : https://prove2.me/theorems/544ffb04-e8f8-49ad-b9f6-e2cebf755947
-- title:
--   Cartwright Steger: cyclic Algebra Norm One To Splitting SL to GL
-- statement:
--   The Cartwright Steger construction uses the cyclic Algebra Norm One To Splitting SL to GL property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/PrasadSpecialization.lean#L5424-L5442
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/PrasadSpecialization.lean#L5424-L5442

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

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.cyclicAlgebraNormOneToSplittingSL_toGL
    (P : BasePrime) (r : Rank) (u : CyclicAlgebraNormOne P r) :
    Matrix.SpecialLinearGroup.toGL
        (cyclicAlgebraNormOneToSplittingSL P r u) =
      cyclicAlgebraUnitToGlobalGL P r u := by sorry
