-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsPetersson_fundamentalDomain_volume_finite
-- name    : QEC.Coding.TannerLiftedProduct.lpsPetersson_fundamentalDomain_volume_finite
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:18:27.78571+00:00
-- url     : https://prove2.me/theorems/06d61805-332d-46da-8244-5da20d63bce6
-- title:
--   Tanner Lifted Product: lps Petersson fundamental Domain volume finite
-- statement:
--   The actual closed modular fundamental domain has finite hyperbolic volume.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSPeterssonMeasure.lean#L41-L61
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSPeterssonMeasure.lean#L41-L61

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

theorem QEC.Coding.TannerLiftedProduct.lpsPetersson_fundamentalDomain_volume_finite : (volume : Measure ℍ) ModularGroup.fd < ⊤ := by sorry
