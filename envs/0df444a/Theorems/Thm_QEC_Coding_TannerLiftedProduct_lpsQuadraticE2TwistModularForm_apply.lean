-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticE2TwistModularForm_apply
-- name    : QEC.Coding.TannerLiftedProduct.lpsQuadraticE2TwistModularForm_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T21:57:37.787929+00:00
-- url     : https://prove2.me/theorems/9e946900-1551-4922-85fc-1b031159f456
-- title:
--   Tanner Lifted Product: lps Quadratic E2 Twist Modular Form apply
-- statement:
--   The genuine modular form retains the actual normalized E2 sum.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuadraticEisensteinModularForm.lean#L336-L337
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuadraticEisensteinModularForm.lean#L336-L337

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuadraticEisensteinSeries
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuadraticEisensteinModularForm
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold

theorem QEC.Coding.TannerLiftedProduct.lpsQuadraticE2TwistModularForm_apply (q : ℕ) [Fact q.Prime] (hq2 : q≠2) (z : ℍ) :
    lpsQuadraticE2TwistModularForm q hq2 z=lpsQuadraticE2Twist q z := by sorry

attribute [defeq] QEC.Coding.TannerLiftedProduct.lpsQuadraticE2TwistModularForm_apply
