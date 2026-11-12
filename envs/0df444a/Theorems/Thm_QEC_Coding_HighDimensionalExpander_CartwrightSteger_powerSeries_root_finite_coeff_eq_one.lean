-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_powerSeries_root_finite_coeff_eq_one
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.powerSeries_root_finite_coeff_eq_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T15:47:06.562358+00:00
-- url     : https://prove2.me/theorems/0407595b-1c00-45a6-8dae-a38416d98e2f
-- title:
--   Cartwright Steger: power Series root finite coeff eq one
-- statement:
--   The Hensel-selected matrix-rank root preserves every finite jet on
--   which its target is already equal to one.  The geometric-series factor is
--   a unit because its constant coefficient is the nonzero matrix rank.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/StrongApproximation.lean#L1867-L1902
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/StrongApproximation.lean#L1867-L1902

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

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.powerSeries_root_finite_coeff_eq_one
    (P : BasePrime) (r : Rank) (level : Nat)
    (a u : PowerSeries (ResidueField P r level)) (n : Nat)
    (haPow : a ^ r.matrixRank = u)
    (haConst : PowerSeries.constantCoeff a = 1)
    (hu : ∀ k < n,
      PowerSeries.coeff k u = PowerSeries.coeff k 1) :
    ∀ k < n, PowerSeries.coeff k a = PowerSeries.coeff k 1 := by sorry
