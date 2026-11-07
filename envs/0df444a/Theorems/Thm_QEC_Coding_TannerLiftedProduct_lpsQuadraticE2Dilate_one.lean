-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticE2Dilate_one
-- name    : QEC.Coding.TannerLiftedProduct.lpsQuadraticE2Dilate_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:01:06.077066+00:00
-- url     : https://prove2.me/theorems/39408d08-6bd2-490d-a6ea-cd66528e582a
-- title:
--   Tanner Lifted Product: lps Quadratic E2 Dilate one
-- statement:
--   Dilation by one has the actual existing quadratic twist as its underlying function.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuadraticEisensteinCuspGeneral.lean#L276-L283
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuadraticEisensteinCuspGeneral.lean#L276-L283

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuadraticEisensteinCusps
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuadraticEisensteinCuspGeneral
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold

theorem QEC.Coding.TannerLiftedProduct.lpsQuadraticE2Dilate_one (q : ℕ) [Fact q.Prime] :
    lpsQuadraticE2Dilate q 1 (by decide)=lpsQuadraticE2Twist q := by sorry
