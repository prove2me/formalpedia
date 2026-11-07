-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_scaled_half_factor
-- name    : QEC.Coding.TannerLiftedProduct.scaled_half_factor
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T21:40:46.144515+00:00
-- url     : https://prove2.me/theorems/bb766f19-c13f-4aed-af5b-6838d1b8f2a0
-- title:
--   Tanner Lifted Product: scaled half factor
-- statement:
--   Positive square scaling contributes its positive square root.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaS.lean#L47-L55
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaS.lean#L47-L55

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSAnalyticTheta
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.ModularForms.Identities
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaS
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm

theorem QEC.Coding.TannerLiftedProduct.scaled_half_factor (r : ℝ) (hr : 0 < r) (z : ℂ) (hz : z ≠ 0) :
    (((r : ℂ)^2) * z) ^ (1 / 2 : ℂ) = (r : ℂ) * z ^ (1 / 2 : ℂ) := by sorry
