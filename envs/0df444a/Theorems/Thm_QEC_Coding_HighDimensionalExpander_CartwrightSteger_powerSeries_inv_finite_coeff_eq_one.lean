-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_powerSeries_inv_finite_coeff_eq_one
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.powerSeries_inv_finite_coeff_eq_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T15:46:18.655681+00:00
-- url     : https://prove2.me/theorems/7ab20fe8-5c9e-494d-9b1c-9b78a052852f
-- title:
--   Cartwright Steger: power Series inv finite coeff eq one
-- statement:
--   Inversion preserves agreement with one through a finite power-series
--   jet, provided the series has constant coefficient one.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/StrongApproximation.lean#L1906-L1936
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/StrongApproximation.lean#L1906-L1936

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

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.powerSeries_inv_finite_coeff_eq_one
    {K : Type*} [Field K] (a : PowerSeries K) (n : Nat)
    (haConst : PowerSeries.constantCoeff a = 1)
    (ha : ∀ k < n,
      PowerSeries.coeff k a = PowerSeries.coeff k 1) :
    ∀ k < n, PowerSeries.coeff k a⁻¹ = PowerSeries.coeff k 1 := by sorry
