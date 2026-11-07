-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQParam_integerWidth_pow
-- name    : QEC.Coding.TannerLiftedProduct.lpsQParam_integerWidth_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:20:21.371198+00:00
-- url     : https://prove2.me/theorems/537bbf0c-c6be-4354-a87e-6a09f0cab935
-- title:
--   Tanner Lifted Product: lps QParam integer Width pow
-- statement:
--   An integer change of Fourier width raises the actual nome to the unit-width nome.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSFourierPeriodChange.lean#L19-L25
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSFourierPeriodChange.lean#L19-L25

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCoefficients
import Mathlib.RingTheory.PowerSeries.Expand
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSFourierPeriodChange
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold Pointwise

theorem QEC.Coding.TannerLiftedProduct.lpsQParam_integerWidth_pow (m : ℕ) (hm : 0 < m) (z : ℍ) :
    Function.Periodic.qParam (m:ℝ) (z:ℂ)^m=Function.Periodic.qParam 1 (z:ℂ) := by sorry
