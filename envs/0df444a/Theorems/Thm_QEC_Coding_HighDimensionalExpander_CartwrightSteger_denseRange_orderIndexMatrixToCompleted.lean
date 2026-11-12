-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_denseRange_orderIndexMatrixToCompleted
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.denseRange_orderIndexMatrixToCompleted
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T16:13:48.887737+00:00
-- url     : https://prove2.me/theorems/587bd3a0-cfed-4750-a875-47498c24ae64
-- title:
--   Cartwright Steger: dense Range order Index Matrix To Completed
-- statement:
--   The construction-owned global cyclic order is dense, as an additive
--   matrix lattice, in its selected completed split matrix algebra.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/StrongApproximation.lean#L3536-L3556
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/StrongApproximation.lean#L3536-L3556

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
open scoped PowerSeries.WithPiTopology
variable (P : BasePrime) (r : Rank) (level : Nat)
attribute [local instance] QEC.Coding.HighDimensionalExpander.CartwrightSteger.residueFieldDiscreteTopologicalSpace
attribute [local instance] QEC.Coding.HighDimensionalExpander.CartwrightSteger.residueFieldDiscreteTopology

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.denseRange_orderIndexMatrixToCompleted :
    DenseRange (fun A : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (ConstantArithmeticRing P r) ↦
      A.map (indexCompletedArithmeticEval P r level)) := by sorry
