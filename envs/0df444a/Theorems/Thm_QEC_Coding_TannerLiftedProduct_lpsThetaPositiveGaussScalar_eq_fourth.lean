-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsThetaPositiveGaussScalar_eq_fourth
-- name    : QEC.Coding.TannerLiftedProduct.lpsThetaPositiveGaussScalar_eq_fourth
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:49:48.406014+00:00
-- url     : https://prove2.me/theorems/b4756011-83ef-40a3-b728-146db6420074
-- title:
--   Tanner Lifted Product: lps Theta Positive Gauss Scalar eq fourth
-- statement:
--   Square scaling reduces the actual four-factor scalar to a single fourth power.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaGaussFourthReduction.lean#L24-L55
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaGaussFourthReduction.lean#L24-L55

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGaussSquare
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaGaussScalar
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaGaussFourthReduction
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Real
open scoped UpperHalfPlane ModularForm MatrixGroups

theorem QEC.Coding.TannerLiftedProduct.lpsThetaPositiveGaussScalar_eq_fourth (q : ℕ) (hq : 0 < q)
    (γ : SL(2,ℤ)) (hc : 0 < γ 1 0) (hlevel : 16*q^2 ∣ (γ 1 0).toNat) :
    lpsThetaPositiveGaussScalar q γ =
      -(4*((γ 1 0).toNat:ℂ)^2)⁻¹ *
        lpsUnaryQuadraticGauss (γ 0 0) (γ 1 0).toNat^4 := by sorry
