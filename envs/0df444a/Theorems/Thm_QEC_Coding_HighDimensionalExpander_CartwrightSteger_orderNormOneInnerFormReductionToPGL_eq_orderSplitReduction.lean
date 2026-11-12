-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_orderNormOneInnerFormReductionToPGL_eq_orderSplitReduction
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.orderNormOneInnerFormReductionToPGL_eq_orderSplitReduction
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T15:50:24.0902+00:00
-- url     : https://prove2.me/theorems/7ec60f66-f6b4-4e23-8003-755538f52ce1
-- title:
--   Cartwright Steger: order Norm One Inner Form Reduction To PGL eq order Split Reduction
-- statement:
--   Compatibility of norm-one reduction with the integral split
--   Cartwright--Steger reduction, before restricting either finite image.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/StrongApproximation.lean#L5316-L5343
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/StrongApproximation.lean#L5316-L5343

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

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.orderNormOneInnerFormReductionToPGL_eq_orderSplitReduction
    (P : BasePrime) (r : Rank) (level : Nat)
    (s : OrderNormOneInnerForm P r) :
    orderNormOneInnerFormReductionToPGL P r level s =
      orderSplitReductionPGLHom P r level
        (orderNormOneInnerFormToSplitGL P r s) := by sorry
