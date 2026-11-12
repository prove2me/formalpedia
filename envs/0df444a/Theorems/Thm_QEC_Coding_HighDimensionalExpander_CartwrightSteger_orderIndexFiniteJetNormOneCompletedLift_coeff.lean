-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_orderIndexFiniteJetNormOneCompletedLift_coeff
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.orderIndexFiniteJetNormOneCompletedLift_coeff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T15:48:06.3273+00:00
-- url     : https://prove2.me/theorems/46501adf-9cc3-47a3-ab66-7040c07bb4b0
-- title:
--   Cartwright Steger: order Index Finite Jet Norm One Completed Lift coeff
-- statement:
--   The local determinant correction does not alter any matrix coefficient
--   below the requested jet precision.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/StrongApproximation.lean#L2897-L2927
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/StrongApproximation.lean#L2897-L2927

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

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.orderIndexFiniteJetNormOneCompletedLift_coeff
    (P : BasePrime) (r : Rank) (level : Nat)
    (s : Matrix.SpecialLinearGroup (Fin r.matrixRank)
      (PowerSeries (ResidueField P r level)))
    (n : Nat) (hn : 0 < n)
    (i j : Fin r.matrixRank) (k : Nat) (hk : k < n) :
    PowerSeries.coeff k
        (orderIndexFiniteJetNormOneCompletedLift P r level s n hn i j) =
      PowerSeries.coeff k
        (((s : Matrix.SpecialLinearGroup (Fin r.matrixRank)
            (PowerSeries (ResidueField P r level))) :
          Matrix (Fin r.matrixRank) (Fin r.matrixRank)
            (PowerSeries (ResidueField P r level))) i j) := by sorry
