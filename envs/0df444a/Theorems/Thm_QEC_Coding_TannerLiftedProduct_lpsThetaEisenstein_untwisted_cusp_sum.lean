-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsThetaEisenstein_untwisted_cusp_sum
-- name    : QEC.Coding.TannerLiftedProduct.lpsThetaEisenstein_untwisted_cusp_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:36:41.417209+00:00
-- url     : https://prove2.me/theorems/32c97949-7d84-4e59-98db-fc08d2195b2e
-- title:
--   Tanner Lifted Product: lps Theta Eisenstein untwisted cusp sum
-- statement:
--   The complete untwisted weighted cusp vector is minus the product of the two true gcd factors.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaEisensteinCusps.lean#L54-L71
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaEisensteinCusps.lean#L54-L71

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaEisensteinCorrection
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCuspLocalFactors
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaEisensteinCusps
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm

theorem QEC.Coding.TannerLiftedProduct.lpsThetaEisenstein_untwisted_cusp_sum (q : ℕ) [Fact q.Prime] (hq2 : q≠2)
    (γ : SL(2,ℤ)) :
    (∑ a : Fin 5,∑ b : Fin 3,
      (lpsThetaEisensteinTwoWeight a*lpsThetaEisensteinPrimeWeight q b)*
        (1-(Int.gcd ((2^a.val*q^b.val:ℕ):ℤ) (γ 1 0):ℂ)^2/((2^a.val*q^b.val:ℕ):ℂ)))=
      -lpsThetaEisensteinTwoCuspFactor γ*lpsThetaEisensteinPrimeCuspFactor q γ := by sorry
