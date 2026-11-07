-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_cpow_pos_real_mul
-- name    : QEC.Coding.TannerLiftedProduct.cpow_pos_real_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T21:40:09.378828+00:00
-- url     : https://prove2.me/theorems/baf580b1-40c3-4088-8f24-3981c425eefb
-- title:
--   Tanner Lifted Product: cpow pos real mul
-- statement:
--   A positive real factor does not change the complex logarithm branch.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaS.lean#L25-L30
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaS.lean#L25-L30

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSAnalyticTheta
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.ModularForms.Identities
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaS
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm

theorem QEC.Coding.TannerLiftedProduct.cpow_pos_real_mul (r : ℝ) (hr : 0 < r) (z s : ℂ) (hz : z ≠ 0) :
    ((r : ℂ) * z) ^ s = (r : ℂ) ^ s * z ^ s := by sorry
