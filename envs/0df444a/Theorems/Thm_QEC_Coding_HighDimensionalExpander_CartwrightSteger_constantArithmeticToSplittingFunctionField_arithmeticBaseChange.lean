-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_constantArithmeticToSplittingFunctionField_arithmeticBaseChange
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.constantArithmeticToSplittingFunctionField_arithmeticBaseChange
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T15:33:57.320802+00:00
-- url     : https://prove2.me/theorems/84dfc488-5be9-49f4-ba40-7aae5d5179a5
-- title:
--   Cartwright Steger: constant Arithmetic To Splitting Function Field arithmetic Base Change
-- statement:
--   The Cartwright Steger construction uses the constant Arithmetic To Splitting Function Field arithmetic Base Change property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/StrongApproximation.lean#L1121-L1144
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/StrongApproximation.lean#L1121-L1144

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_SimpleTransitivity
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Projective_SpecialLinear
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Order_Reduction
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_CyclicDivisionAlgebra
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.PiTopology
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.RingTheory.TensorProduct.Free
import Mathlib.Algebra.Central.Matrix
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_StrongApproximation
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups SphericalHecke.LocalTopology Valued

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.constantArithmeticToSplittingFunctionField_arithmeticBaseChange
    (P : BasePrime) (r : Rank) (a : ArithmeticRing P) :
    constantArithmeticToSplittingFunctionField P r
        (arithmeticToConstantArithmetic P r a) =
      arithmeticRingToSplittingFunctionField P r a := by sorry
