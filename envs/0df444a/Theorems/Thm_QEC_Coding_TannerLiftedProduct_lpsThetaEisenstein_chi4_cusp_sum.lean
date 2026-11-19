-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsThetaEisenstein_chi4_cusp_sum
-- name    : QEC.Coding.TannerLiftedProduct.lpsThetaEisenstein_chi4_cusp_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:37:03.588389+00:00
-- url     : https://prove2.me/theorems/d69902c6-5eea-458f-9720-732e410401c5
-- title:
--   Tanner Lifted Product: lps Theta Eisenstein chi4 cusp sum
-- statement:
--   The complete modulus-four dilation coefficients sum to the negative prime-power gcd factor.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaEisensteinCusps.lean#L102-L116
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaEisensteinCusps.lean#L102-L116

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaEisensteinCorrection
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCuspLocalFactors
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaEisensteinCusps
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm

theorem QEC.Coding.TannerLiftedProduct.lpsThetaEisenstein_chi4_cusp_sum (q : ℕ) [Fact q.Prime] (γ : SL(2,ℤ)) :
    (∑ b : Fin 3,lpsThetaEisensteinChi4Weight q b*
      ((Int.gcd ((q^b.val:ℕ):ℤ) (γ 1 0):ℂ)^2/((q^b.val:ℕ):ℂ)^2))=
      -lpsThetaEisensteinPrimeCuspFactor q γ := by sorry
