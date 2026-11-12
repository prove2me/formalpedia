-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_exists_orderMatrix_finiteJetLift_special
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.exists_orderMatrix_finiteJetLift_special
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T16:11:53.510071+00:00
-- url     : https://prove2.me/theorems/553d57ad-3ece-4ccb-9fae-abec18d913f7
-- title:
--   Cartwright Steger: exists order Matrix finite Jet Lift special
-- statement:
--   Combined finite-jet approximation inside the genuine arithmetic order.
--   For every completed special-linear point and every precision, this produces
--   one global order matrix whose entries match the point and whose reduced norm
--   matches one to the same precision.  No global invertibility or exact norm-one
--   claim is hidden in this statement.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/StrongApproximation.lean#L2748-L2780
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/StrongApproximation.lean#L2748-L2780

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

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.exists_orderMatrix_finiteJetLift_special
    (P : BasePrime) (r : Rank) (level : Nat)
    (s : Matrix.SpecialLinearGroup (Fin r.matrixRank)
      (PowerSeries (ResidueField P r level)))
    (n : Nat) :
    ∃ A : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (ConstantArithmeticRing P r),
      A.map (constantArithmeticToSplittingFunctionField P r) ∈
          CartwrightStegerOrder P r ∧
      (∀ (i j : Fin r.matrixRank) (k : Nat), k < n →
        PowerSeries.coeff k
            ((A.map (indexCompletedArithmeticEval P r level)) i j) =
          PowerSeries.coeff k
            (((s : Matrix.SpecialLinearGroup (Fin r.matrixRank)
                (PowerSeries (ResidueField P r level))) :
              Matrix (Fin r.matrixRank) (Fin r.matrixRank)
                (PowerSeries (ResidueField P r level))) i j)) ∧
      (∀ k : Nat, k < n →
        PowerSeries.coeff k
            (Matrix.det
              (A.map (indexCompletedArithmeticEval P r level))) =
          PowerSeries.coeff k 1) := by sorry
