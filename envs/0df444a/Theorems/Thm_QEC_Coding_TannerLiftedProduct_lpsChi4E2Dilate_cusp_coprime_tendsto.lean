-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsChi4E2Dilate_cusp_coprime_tendsto
-- name    : QEC.Coding.TannerLiftedProduct.lpsChi4E2Dilate_cusp_coprime_tendsto
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:07:38.184357+00:00
-- url     : https://prove2.me/theorems/e4f799a2-503a-44fb-9e72-e0e2d3c14593
-- title:
--   Tanner Lifted Product: lps Chi4 E2 Dilate cusp coprime tendsto
-- statement:
--   The actual modulus-four unit dilation cusp limit is its original character constant times the derived gcd factor.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCharacterEisensteinDilation.lean#L259-L266
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCharacterEisensteinDilation.lean#L259-L266

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCharacterEisensteinCusps
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCharacterEisensteinDilation
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm

theorem QEC.Coding.TannerLiftedProduct.lpsChi4E2Dilate_cusp_coprime_tendsto (m : ℕ) (hm : 0<m)
    (hm4 : m.Coprime 4) (γ : SL(2,ℤ)) :
    Tendsto (lpsChi4E2Dilate m hm ∣[(2:ℤ)] γ) UpperHalfPlane.atImInfty
      (𝓝 (((Int.gcd (m:ℤ) (γ 1 0):ℂ)^2/(m:ℂ)^2)*
        (lpsChi4E2Character (m:ZMod 4)*lpsChi4EisensteinCuspConstant γ))) := by sorry
