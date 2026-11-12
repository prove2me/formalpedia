-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_exists_indexCompletedPolynomialEval_finite_coeff_lift
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.exists_indexCompletedPolynomialEval_finite_coeff_lift
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T15:47:35.904437+00:00
-- url     : https://prove2.me/theorems/d1619227-6b01-4772-8411-fb744b59e1f7
-- title:
--   Cartwright Steger: exists index Completed Polynomial Eval finite coeff lift
-- statement:
--   Every finite coefficient jet in the selected complete local coefficient
--   ring has a polynomial lift.  The induction corrects one coefficient at a
--   time with a power of the construction-owned closed-point uniformizer.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/StrongApproximation.lean#L2147-L2205
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/StrongApproximation.lean#L2147-L2205

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

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.exists_indexCompletedPolynomialEval_finite_coeff_lift
    (P : BasePrime) (r : Rank) (level : Nat)
    (s : PowerSeries (ResidueField P r level)) (n : Nat) :
    ∃ f : ConstantPolynomialRing P r, ∀ k < n,
      PowerSeries.coeff k (indexCompletedPolynomialEval P r level f) =
        PowerSeries.coeff k s := by sorry
