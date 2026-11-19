-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsThetaEisenstein_quadratic_cusp_sum
-- name    : QEC.Coding.TannerLiftedProduct.lpsThetaEisenstein_quadratic_cusp_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:37:13.749322+00:00
-- url     : https://prove2.me/theorems/5d25fd64-4339-4842-94ff-52619925cffd
-- title:
--   Tanner Lifted Product: lps Theta Eisenstein quadratic cusp sum
-- statement:
--   The complete prime-character dilation coefficients sum to the negative two-power gcd factor.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaEisensteinCusps.lean#L119-L136
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaEisensteinCusps.lean#L119-L136

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaEisensteinCorrection
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCuspLocalFactors
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaEisensteinCusps
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm

theorem QEC.Coding.TannerLiftedProduct.lpsThetaEisenstein_quadratic_cusp_sum (q : ℕ) [Fact q.Prime] (hq2 : q≠2)
    (γ : SL(2,ℤ)) :
    (∑ a : Fin 5,lpsThetaEisensteinQuadraticWeight q a*
      ((Int.gcd ((2^a.val:ℕ):ℤ) (γ 1 0):ℂ)^2/((2^a.val:ℕ):ℂ)^2)*
        lpsQuadraticE2Character q ((2^a.val:ℕ):ZMod q))=
      -lpsThetaEisensteinTwoCuspFactor γ := by sorry
