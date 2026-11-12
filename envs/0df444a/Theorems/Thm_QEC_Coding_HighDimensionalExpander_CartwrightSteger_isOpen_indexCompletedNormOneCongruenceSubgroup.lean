-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_isOpen_indexCompletedNormOneCongruenceSubgroup
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.isOpen_indexCompletedNormOneCongruenceSubgroup
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T16:15:16.020692+00:00
-- url     : https://prove2.me/theorems/b9c12d34-496d-4a37-98f9-99cca1267b2d
-- title:
--   Cartwright Steger: is Open index Completed Norm One Congruence Subgroup
-- statement:
--   The principal local norm-one congruence subgroup is open in the actual
--   completed cyclic-order group.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/StrongApproximation.lean#L3636-L3642
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/StrongApproximation.lean#L3636-L3642

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

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.isOpen_indexCompletedNormOneCongruenceSubgroup :
    IsOpen (IndexCompletedNormOneCongruenceSubgroup P r level :
      Set (IndexCompletedNormOneInnerForm P r level)) := by sorry
