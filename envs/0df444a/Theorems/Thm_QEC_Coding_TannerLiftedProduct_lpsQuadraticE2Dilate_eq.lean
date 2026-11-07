-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticE2Dilate_eq
-- name    : QEC.Coding.TannerLiftedProduct.lpsQuadraticE2Dilate_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:01:14.301727+00:00
-- url     : https://prove2.me/theorems/f49e8764-fa75-487a-a38a-f0b30137d9e8
-- title:
--   Tanner Lifted Product: lps Quadratic E2 Dilate eq
-- statement:
--   Actual translation compatibility expands the dilated twist into its genuine finite E2 sum.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuadraticEisensteinCuspGeneral.lean#L238-L244
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuadraticEisensteinCuspGeneral.lean#L238-L244

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuadraticEisensteinCusps
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuadraticEisensteinCuspGeneral
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold

theorem QEC.Coding.TannerLiftedProduct.lpsQuadraticE2Dilate_eq (q m : ℕ) [Fact q.Prime] (hm : 0<m) :
    lpsQuadraticE2Dilate q m hm = (fun z : ℍ =>
      (gaussSum (lpsQuadraticE2Character q) (ZMod.stdAddChar (N:=q)))⁻¹ *
        ∑ r : Fin q,lpsQuadraticE2Character q (r.val:ZMod q)*
          EisensteinSeries.E2 (lpsE2AffineMatrix m hm ((r.val:ℝ)/(q:ℝ)) • z)) := by sorry
