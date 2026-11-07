-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHorocyclePoint_continuous
-- name    : QEC.Coding.TannerLiftedProduct.lpsHorocyclePoint_continuous
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:05:27.599199+00:00
-- url     : https://prove2.me/theorems/848911fd-7fc5-461d-8c47-61a98f5f7f5f
-- title:
--   Tanner Lifted Product: lps Horocycle Point continuous
-- statement:
--   The actual horizontal parametrization is continuous.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCuspHorocycle.lean#L25-L33
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCuspHorocycle.lean#L25-L33

import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.NumberTheory.ModularForms.Bounds
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspHorocycle
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology MeasureTheory Asymptotics
open scoped MatrixGroups UpperHalfPlane ModularForm

theorem QEC.Coding.TannerLiftedProduct.lpsHorocyclePoint_continuous (y : ℝ) (hy : 0<y) :
    Continuous (lpsHorocyclePoint y hy) := by sorry
