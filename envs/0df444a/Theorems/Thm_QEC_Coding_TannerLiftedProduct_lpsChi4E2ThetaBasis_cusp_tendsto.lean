-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsChi4E2ThetaBasis_cusp_tendsto
-- name    : QEC.Coding.TannerLiftedProduct.lpsChi4E2ThetaBasis_cusp_tendsto
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:39:17.561508+00:00
-- url     : https://prove2.me/theorems/6e31b5e1-281f-482c-b092-8865f51e09a6
-- title:
--   Tanner Lifted Product: lps Chi4 E2 Theta Basis cusp tendsto
-- statement:
--   Every actual common-level modulus-four basis form has its proved gcd-scaled cusp constant.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaEisensteinCusps.lean#L149-L159
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaEisensteinCusps.lean#L149-L159

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaEisensteinCorrection
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCuspLocalFactors
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaEisensteinCusps
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm

theorem QEC.Coding.TannerLiftedProduct.lpsChi4E2ThetaBasis_cusp_tendsto (q : ℕ) [Fact q.Prime] (hq4 : q%4=1)
    (b : Fin 3) (γ : SL(2,ℤ)) :
    Tendsto ((lpsChi4E2ThetaBasis q b : ℍ→ℂ) ∣[(2:ℤ)] γ) UpperHalfPlane.atImInfty
      (𝓝 (((Int.gcd ((q^b.val:ℕ):ℤ) (γ 1 0):ℂ)^2/((q^b.val:ℕ):ℂ)^2)*
        lpsChi4EisensteinCuspConstant γ)) := by sorry
