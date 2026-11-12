-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_orderIndexMatrixLift_to_global
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.orderIndexMatrixLift_to_global
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T15:46:24.909235+00:00
-- url     : https://prove2.me/theorems/c496e2ff-fa95-4778-be2b-208c50e13d2b
-- title:
--   Cartwright Steger: order Index Matrix Lift to global
-- statement:
--   The Cartwright Steger construction uses the order Index Matrix Lift to global property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/StrongApproximation.lean#L1573-L1603
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/StrongApproximation.lean#L1573-L1603

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

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.orderIndexMatrixLift_to_global
    (P : BasePrime) (r : Rank) (level : Nat)
    (A : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (ResidueField P r level)) :
    (orderIndexMatrixLift P r level A).map
        (constantArithmeticToSplittingFunctionField P r) =
      ∑ p : Fin r.matrixRank × Fin r.matrixRank,
        arithmeticRingToSplittingFunctionField P r
            (indexArithmeticCoefficientLift P r level
              ((indexCyclicBasis P r level).repr A p)) •
          splittingCyclicBasisVector P r p := by sorry
