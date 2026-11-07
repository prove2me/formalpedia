-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsE2AffineMatrix_qParam
-- name    : QEC.Coding.TannerLiftedProduct.lpsE2AffineMatrix_qParam
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:12:29.322291+00:00
-- url     : https://prove2.me/theorems/c70bedac-d411-4fbf-a2e8-0b674bfeefbf
-- title:
--   Tanner Lifted Product: lps E2 Affine Matrix q Param
-- statement:
--   The actual dilation action and exponential law give the true m-th-power nome.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSEisensteinDifference.lean#L202-L208
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSEisensteinDifference.lean#L202-L208

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuadraticEisensteinCuspGeneral
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEisensteinDifference
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold

theorem QEC.Coding.TannerLiftedProduct.lpsE2AffineMatrix_qParam (m : ℕ) (hm : 0 < m) (z : ℍ) :
    Function.Periodic.qParam 1 ((lpsE2AffineMatrix m hm 0 • z:ℍ):ℂ)=
      Function.Periodic.qParam 1 (z:ℂ)^m := by sorry
