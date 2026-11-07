-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckeQParam_pow
-- name    : QEC.Coding.TannerLiftedProduct.lpsHeckeQParam_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:18:20.539609+00:00
-- url     : https://prove2.me/theorems/b984ff99-a0e3-4890-bde3-d8bb6af29ae1
-- title:
--   Tanner Lifted Product: lps Hecke QParam pow
-- statement:
--   Taking the p-th power of the p-width nome recovers the unit-width nome.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckeCoefficients.lean#L60-L66
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckeCoefficients.lean#L60-L66

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspHecke
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckePolynomial
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCoefficients
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold

theorem QEC.Coding.TannerLiftedProduct.lpsHeckeQParam_pow (p : ℕ) [Fact p.Prime] (z : ℍ) :
    Function.Periodic.qParam (p:ℝ) (z:ℂ)^p=Function.Periodic.qParam 1 (z:ℂ) := by sorry
