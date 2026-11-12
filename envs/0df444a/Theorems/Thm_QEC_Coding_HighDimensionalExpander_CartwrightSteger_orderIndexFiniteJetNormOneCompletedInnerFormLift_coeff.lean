-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_orderIndexFiniteJetNormOneCompletedInnerFormLift_coeff
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.orderIndexFiniteJetNormOneCompletedInnerFormLift_coeff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T16:12:14.027509+00:00
-- url     : https://prove2.me/theorems/c5c506d1-3e81-4aa0-92bf-b717f9c65685
-- title:
--   Cartwright Steger: order Index Finite Jet Norm One Completed Inner Form Lift coeff
-- statement:
--   Every completed norm-one point is matched to arbitrary precision by the
--   Hensel correction of an actual global arithmetic-order matrix.  The scalar
--   correction still lives in the completion; descending that correction to a
--   global norm-one unit is the remaining strong-approximation step.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/StrongApproximation.lean#L3240-L3258
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/StrongApproximation.lean#L3240-L3258

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

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.orderIndexFiniteJetNormOneCompletedInnerFormLift_coeff
    (P : BasePrime) (r : Rank) (level : Nat)
    (s : IndexCompletedNormOneInnerForm P r level)
    (n : Nat) (hn : 0 < n)
    (i j : Fin r.matrixRank) (k : Nat) (hk : k < n) :
    PowerSeries.coeff k
        (((orderIndexFiniteJetNormOneCompletedInnerFormLift
            P r level s n hn :
          Matrix.SpecialLinearGroup (Fin r.matrixRank)
            (PowerSeries (ResidueField P r level))) :
          Matrix (Fin r.matrixRank) (Fin r.matrixRank)
            (PowerSeries (ResidueField P r level))) i j) =
      PowerSeries.coeff k
        (((s : Matrix.SpecialLinearGroup (Fin r.matrixRank)
            (PowerSeries (ResidueField P r level))) :
          Matrix (Fin r.matrixRank) (Fin r.matrixRank)
            (PowerSeries (ResidueField P r level))) i j) := by sorry
