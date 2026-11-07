-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticE2Dilate_cusp_coprime_tendsto
-- name    : QEC.Coding.TannerLiftedProduct.lpsQuadraticE2Dilate_cusp_coprime_tendsto
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:06:50.612876+00:00
-- url     : https://prove2.me/theorems/dc0de027-d7ae-4099-8ec2-b615a575d49e
-- title:
--   Tanner Lifted Product: lps Quadratic E2 Dilate cusp coprime tendsto
-- statement:
--   The actual prime-unit dilation cusp limit is its original character constant times the derived gcd factor.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCharacterEisensteinDilation.lean#L249-L256
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCharacterEisensteinDilation.lean#L249-L256

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCharacterEisensteinCusps
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCharacterEisensteinDilation
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm

theorem QEC.Coding.TannerLiftedProduct.lpsQuadraticE2Dilate_cusp_coprime_tendsto (q m : ℕ) [Fact q.Prime]
    (hq2 : q≠2) (hm : 0<m) (hmq : m.Coprime q) (γ : SL(2,ℤ)) :
    Tendsto (lpsQuadraticE2Dilate q m hm ∣[(2:ℤ)] γ) UpperHalfPlane.atImInfty
      (𝓝 (((Int.gcd (m:ℤ) (γ 1 0):ℂ)^2/(m:ℂ)^2)*
        (lpsQuadraticE2Character q (m:ZMod q)*lpsQuadraticEisensteinCuspConstant q γ))) := by sorry
