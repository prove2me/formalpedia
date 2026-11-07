-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsPetersson_im_inverse_square_integrable
-- name    : QEC.Coding.TannerLiftedProduct.lpsPetersson_im_inverse_square_integrable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:18:23.754644+00:00
-- url     : https://prove2.me/theorems/749df4bd-7a13-45fe-8c52-2df25936219b
-- title:
--   Tanner Lifted Product: lps Petersson im inverse square integrable
-- statement:
--   The inverse-square height density is integrable above every positive height.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSPeterssonMeasure.lean#L20-L24
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSPeterssonMeasure.lean#L20-L24

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspHorocycle
import Mathlib.Analysis.Complex.UpperHalfPlane.Measure
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSPeterssonMeasure
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Asymptotics Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ComplexConjugate
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsPetersson_im_inverse_square_integrable (a : ℝ) (ha : 0<a) :
    IntegrableOn (fun y : ℝ => (1/y)^2) (Ioi a) := by sorry
