-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsE2Affine_cusp_tendsto
-- name    : QEC.Coding.TannerLiftedProduct.lpsE2Affine_cusp_tendsto
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:01:19.861202+00:00
-- url     : https://prove2.me/theorems/d37f903d-86ff-4e67-a2b1-f1f70fe5ad9b
-- title:
--   Tanner Lifted Product: lps E2 Affine cusp tendsto
-- statement:
--   The actual affine times cusp matrix and constructed primitive column give its full-filter gcd constant.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuadraticEisensteinCuspGeneral.lean#L167-L223
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuadraticEisensteinCuspGeneral.lean#L167-L223

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuadraticEisensteinCusps
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuadraticEisensteinCuspGeneral
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold

theorem QEC.Coding.TannerLiftedProduct.lpsE2Affine_cusp_tendsto (m q : ℕ) (hm : 0<m) (hq : 0<q)
    (r : ℤ) (γ : SL(2,ℤ)) :
    Tendsto ((fun z : ℍ => EisensteinSeries.E2
        (lpsE2AffineMatrix m hm ((r:ℝ)/(q:ℝ)) • z)) ∣[(2:ℤ)] γ)
      UpperHalfPlane.atImInfty
      (𝓝 (((Int.gcd ((q:ℤ)*(m:ℤ)*γ 0 0+r*γ 1 0) ((q:ℤ)*γ 1 0):ℕ):ℂ)^2/
        ((q:ℂ)^2*(m:ℂ)^2))) := by sorry
