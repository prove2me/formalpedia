-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cyclicAlgebraNormOneToSplittingSL_order_compatibility
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.cyclicAlgebraNormOneToSplittingSL_order_compatibility
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T17:47:25.806201+00:00
-- url     : https://prove2.me/theorems/6b7fa30c-dd9b-4271-9265-4740b913bd6f
-- title:
--   Cartwright Steger: cyclic Algebra Norm One To Splitting SL order compatibility
-- statement:
--   The Cartwright Steger construction uses the cyclic Algebra Norm One To Splitting SL order compatibility property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/PrasadSpecialization.lean#L5458-L5472
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/PrasadSpecialization.lean#L5458-L5472

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

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.cyclicAlgebraNormOneToSplittingSL_order_compatibility
    (P : BasePrime) (r : Rank) (s : OrderNormOneInnerForm P r) :
    cyclicAlgebraNormOneToSplittingSL P r
        (orderNormOneInnerFormToCyclicAlgebraNormOne P r s) =
      Matrix.SpecialLinearGroup.map (n := Fin r.matrixRank)
        (constantArithmeticToSplittingFunctionField P r)
        (s : Matrix.SpecialLinearGroup (Fin r.matrixRank)
          (ConstantArithmeticRing P r)) := by sorry
