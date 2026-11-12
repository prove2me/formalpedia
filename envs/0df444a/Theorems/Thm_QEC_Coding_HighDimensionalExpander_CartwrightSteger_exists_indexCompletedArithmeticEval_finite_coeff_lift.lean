-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_exists_indexCompletedArithmeticEval_finite_coeff_lift
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.exists_indexCompletedArithmeticEval_finite_coeff_lift
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T15:47:05.750075+00:00
-- url     : https://prove2.me/theorems/8480ed3a-fb2f-44d1-b6f9-06ad8e0c3b0f
-- title:
--   Cartwright Steger: exists index Completed Arithmetic Eval finite coeff lift
-- statement:
--   The localized arithmetic coefficient ring realizes every finite jet in
--   the selected completion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/StrongApproximation.lean#L2393-L2405
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/StrongApproximation.lean#L2393-L2405

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

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.exists_indexCompletedArithmeticEval_finite_coeff_lift
    (P : BasePrime) (r : Rank) (level : Nat)
    (s : PowerSeries (ResidueField P r level)) (n : Nat) :
    ∃ a : ConstantArithmeticRing P r, ∀ k < n,
      PowerSeries.coeff k (indexCompletedArithmeticEval P r level a) =
        PowerSeries.coeff k s := by sorry
