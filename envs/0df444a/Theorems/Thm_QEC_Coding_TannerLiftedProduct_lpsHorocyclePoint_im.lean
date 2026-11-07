-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHorocyclePoint_im
-- name    : QEC.Coding.TannerLiftedProduct.lpsHorocyclePoint_im
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:15:27.671288+00:00
-- url     : https://prove2.me/theorems/5a81af57-02d5-4d84-b580-cbb9490fd7dc
-- title:
--   Tanner Lifted Product: lps Horocycle Point im
-- statement:
--   The horizontal point has exactly the specified height.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCuspHorocycle.lean#L21-L22
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCuspHorocycle.lean#L21-L22

import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.NumberTheory.ModularForms.Bounds
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspHorocycle
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology MeasureTheory Asymptotics
open scoped MatrixGroups UpperHalfPlane ModularForm

theorem QEC.Coding.TannerLiftedProduct.lpsHorocyclePoint_im (y : ℝ) (hy : 0<y) (x : ℝ) :
    (lpsHorocyclePoint y hy x).im=y := by sorry

attribute [defeq] QEC.Coding.TannerLiftedProduct.lpsHorocyclePoint_im
