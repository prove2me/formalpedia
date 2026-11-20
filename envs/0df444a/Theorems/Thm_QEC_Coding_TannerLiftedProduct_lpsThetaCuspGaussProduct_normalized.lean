-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsThetaCuspGaussProduct_normalized
-- name    : QEC.Coding.TannerLiftedProduct.lpsThetaCuspGaussProduct_normalized
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:39:26.722896+00:00
-- url     : https://prove2.me/theorems/69967aac-44b5-457f-9820-66629d37f366
-- title:
--   Tanner Lifted Product: lps Theta Cusp Gauss Product normalized
-- statement:
--   Normalize the full Gauss product to exactly the true Eisenstein correction constant.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaCuspFactorization.lean#L340-L355
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaCuspFactorization.lean#L340-L355

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaEisensteinCusps
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCuspFactorization
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm

theorem QEC.Coding.TannerLiftedProduct.lpsThetaCuspGaussProduct_normalized (q N : ℕ) [Fact q.Prime]
    (hq4 : q%4=1) (hN : 0<N) (γ : SL(2,ℤ)) (hC : γ 1 0=(N:ℤ)) :
    -(32*(q:ℂ)^3*(N:ℂ)^2)⁻¹*lpsThetaCuspGaussProduct q (γ 0 0) N=
      -lpsThetaEisensteinNormalization q*
        (lpsThetaEisensteinTwoCuspFactor γ+lpsChi4EisensteinCuspConstant γ)*
        (lpsThetaEisensteinPrimeCuspFactor q γ+lpsQuadraticEisensteinCuspConstant q γ) := by sorry
