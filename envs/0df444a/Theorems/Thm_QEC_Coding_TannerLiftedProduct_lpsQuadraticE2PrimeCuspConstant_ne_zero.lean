-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticE2PrimeCuspConstant_ne_zero
-- name    : QEC.Coding.TannerLiftedProduct.lpsQuadraticE2PrimeCuspConstant_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:00:57.558205+00:00
-- url     : https://prove2.me/theorems/e5f539d5-f2b4-4078-ac58-3e78326ec7ad
-- title:
--   Tanner Lifted Product: lps Quadratic E2 Prime Cusp Constant ne zero
-- statement:
--   Actual character and Gauss units plus q greater than one make the cusp constant nonzero.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuadraticEisensteinCusps.lean#L297-L305
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuadraticEisensteinCusps.lean#L297-L305

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuadraticEisensteinModularForm
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuadraticEisensteinCusps
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold

theorem QEC.Coding.TannerLiftedProduct.lpsQuadraticE2PrimeCuspConstant_ne_zero (q : ℕ) [Fact q.Prime] (hq2 : q≠2) :
    lpsQuadraticE2Character q (-1:ZMod q)*((q:ℂ)^2-1)/
      gaussSum (lpsQuadraticE2Character q) (ZMod.stdAddChar (N:=q))≠0 := by sorry
