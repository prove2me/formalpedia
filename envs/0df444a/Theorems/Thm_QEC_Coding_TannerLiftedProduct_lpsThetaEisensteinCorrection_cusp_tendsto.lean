-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsThetaEisensteinCorrection_cusp_tendsto
-- name    : QEC.Coding.TannerLiftedProduct.lpsThetaEisensteinCorrection_cusp_tendsto
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:37:30.632686+00:00
-- url     : https://prove2.me/theorems/c6d5d70a-e2fc-4fe3-a96d-3acb10961d38
-- title:
--   Tanner Lifted Product: lps Theta Eisenstein Correction cusp tendsto
-- statement:
--   At every integer cusp matrix the actual correction has the complete factored gcd-character constant.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaEisensteinCusps.lean#L193-L245
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaEisensteinCusps.lean#L193-L245

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaEisensteinCorrection
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCuspLocalFactors
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaEisensteinCusps
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm

theorem QEC.Coding.TannerLiftedProduct.lpsThetaEisensteinCorrection_cusp_tendsto (q : ℕ) [Fact q.Prime] (hq4 : q%4=1)
    (γ : SL(2,ℤ)) :
    Tendsto ((lpsThetaEisensteinCorrection q (by intro h;subst q;norm_num at hq4) : ℍ→ℂ)
      ∣[(2:ℤ)] γ) UpperHalfPlane.atImInfty
      (𝓝 (-lpsThetaEisensteinNormalization q *
        (lpsThetaEisensteinTwoCuspFactor γ+lpsChi4EisensteinCuspConstant γ)*
        (lpsThetaEisensteinPrimeCuspFactor q γ+lpsQuadraticEisensteinCuspConstant q γ))) := by sorry
