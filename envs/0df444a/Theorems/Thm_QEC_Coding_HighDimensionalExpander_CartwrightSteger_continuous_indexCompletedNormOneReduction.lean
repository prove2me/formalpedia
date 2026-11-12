-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_continuous_indexCompletedNormOneReduction
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.continuous_indexCompletedNormOneReduction
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T15:48:08.627014+00:00
-- url     : https://prove2.me/theorems/c4f02420-4cbc-442e-9c3e-34b912fbc9f9
-- title:
--   Cartwright Steger: continuous index Completed Norm One Reduction
-- statement:
--   Constant-coefficient reduction is continuous for the coefficientwise
--   topology on the selected completed norm-one cyclic order.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/StrongApproximation.lean#L3617-L3632
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/StrongApproximation.lean#L3617-L3632

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

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.continuous_indexCompletedNormOneReduction :
    Continuous (indexCompletedNormOneReduction P r level) := by sorry
