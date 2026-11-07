-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsPetersson_complex_strip_inverse_square_integrable
-- name    : QEC.Coding.TannerLiftedProduct.lpsPetersson_complex_strip_inverse_square_integrable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:18:29.383698+00:00
-- url     : https://prove2.me/theorems/105d3718-3e64-4e6f-81ba-1fb7b07fc8fd
-- title:
--   Tanner Lifted Product: lps Petersson complex strip inverse square integrable
-- statement:
--   The actual inverse-square height density is integrable on the containing vertical strip.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSPeterssonMeasure.lean#L27-L38
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSPeterssonMeasure.lean#L27-L38

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

theorem QEC.Coding.TannerLiftedProduct.lpsPetersson_complex_strip_inverse_square_integrable :
    IntegrableOn (fun z : ℂ => (1/z.im)^2)
      (Complex.measurableEquivRealProd ⁻¹' (Icc (-1/2:ℝ) (1/2) ×ˢ Ioi (1/2:ℝ))) := by sorry
