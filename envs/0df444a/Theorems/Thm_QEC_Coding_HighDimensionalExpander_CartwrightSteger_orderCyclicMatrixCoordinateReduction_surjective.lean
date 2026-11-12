-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_orderCyclicMatrixCoordinateReduction_surjective
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.orderCyclicMatrixCoordinateReduction_surjective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T16:11:55.233181+00:00
-- url     : https://prove2.me/theorems/e0a8d150-9f46-4aa9-a70e-4d6c246cf66c
-- title:
--   Cartwright Steger: order Cyclic Matrix Coordinate Reduction surjective
-- statement:
--   Every finite matrix has a lift in the actual descended cyclic order.
--   This is ring-level lifting; promotion of an invertible finite matrix to a
--   global order unit is the separate strong-approximation step.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/StrongApproximation.lean#L2979-L2990
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/StrongApproximation.lean#L2979-L2990

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

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.orderCyclicMatrixCoordinateReduction_surjective
    (P : BasePrime) (r : Rank) (level : Nat) :
    Function.Surjective
      (orderCyclicMatrixCoordinateReduction P r level) := by sorry
