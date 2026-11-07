-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticE2PrimeCusp_sum
-- name    : QEC.Coding.TannerLiftedProduct.lpsQuadraticE2PrimeCusp_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:01:02.444526+00:00
-- url     : https://prove2.me/theorems/28faa32a-9809-4551-adda-7e17e1f9dc8c
-- title:
--   Tanner Lifted Product: lps Quadratic E2 Prime Cusp sum
-- statement:
--   The actual zero character sum and exceptional residue compute the weighted cusp constant.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuadraticEisensteinCusps.lean#L235-L262
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuadraticEisensteinCusps.lean#L235-L262

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuadraticEisensteinModularForm
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuadraticEisensteinCusps
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold

theorem QEC.Coding.TannerLiftedProduct.lpsQuadraticE2PrimeCusp_sum (q : ℕ) [Fact q.Prime] (hq2 : q≠2) :
    (∑ r : Fin q,lpsQuadraticE2Character q (r.val:ZMod q)*
      (if r.val+1=q then (q:ℂ)^2 else 1)) =
        lpsQuadraticE2Character q (-1:ZMod q)*((q:ℂ)^2-1) := by sorry
