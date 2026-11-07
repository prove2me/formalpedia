-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsWeightTwoPetersson_self
-- name    : QEC.Coding.TannerLiftedProduct.lpsWeightTwoPetersson_self
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:20:31.759243+00:00
-- url     : https://prove2.me/theorems/bdbbd3f6-4f83-419c-ade0-63f829cb5468
-- title:
--   Tanner Lifted Product: lps Weight Two Petersson self
-- statement:
--   The weight-two self-integrand is the actual squared norm times height squared.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCuspPeterssonTrace.lean#L119-L122
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCuspPeterssonTrace.lean#L119-L122

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSPeterssonMeasure
import Mathlib.Data.Finset.Lattice.Fold
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspPeterssonTrace
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Asymptotics Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ComplexConjugate
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsWeightTwoPetersson_self (f : ℍ → ℂ) (τ : ℍ) :
    petersson 2 f f τ = ((‖f τ‖^2*τ.im^2:ℝ):ℂ) := by sorry
