-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsFourier_one_pow
-- name    : QEC.Coding.TannerLiftedProduct.lpsFourier_one_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:17:59.291196+00:00
-- url     : https://prove2.me/theorems/bfa24ad8-77e0-439b-a13b-0583cba71695
-- title:
--   Tanner Lifted Product: lps Fourier one pow
-- statement:
--   Natural powers of the first period-one Fourier character are the corresponding actual frequencies.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCuspHorocycle.lean#L80-L85
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCuspHorocycle.lean#L80-L85

import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.NumberTheory.ModularForms.Bounds
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspHorocycle
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology MeasureTheory Asymptotics
open scoped MatrixGroups UpperHalfPlane ModularForm

theorem QEC.Coding.TannerLiftedProduct.lpsFourier_one_pow (n : ℕ) (x : ℝ) :
    (fourier (1:ℤ) (x:AddCircle (1:ℝ)))^n=fourier (n:ℤ) (x:AddCircle (1:ℝ)) := by sorry
