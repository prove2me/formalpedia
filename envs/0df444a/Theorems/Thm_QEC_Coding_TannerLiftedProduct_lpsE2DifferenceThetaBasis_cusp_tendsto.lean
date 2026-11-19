-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsE2DifferenceThetaBasis_cusp_tendsto
-- name    : QEC.Coding.TannerLiftedProduct.lpsE2DifferenceThetaBasis_cusp_tendsto
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:37:28.426326+00:00
-- url     : https://prove2.me/theorems/3f49940d-b0b9-443d-bc57-249129c4d7ba
-- title:
--   Tanner Lifted Product: lps E2 Difference Theta Basis cusp tendsto
-- statement:
--   Every actual common-level E2 difference has its full signed denominator-gcd cusp limit.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaEisensteinCusps.lean#L139-L146
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaEisensteinCusps.lean#L139-L146

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaEisensteinCorrection
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCuspLocalFactors
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaEisensteinCusps
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm

theorem QEC.Coding.TannerLiftedProduct.lpsE2DifferenceThetaBasis_cusp_tendsto (q : ℕ) [Fact q.Prime]
    (a : Fin 5) (b : Fin 3) (γ : SL(2,ℤ)) :
    Tendsto ((lpsE2DifferenceThetaBasis q a b : ℍ→ℂ) ∣[(2:ℤ)] γ) UpperHalfPlane.atImInfty
      (𝓝 (1-(Int.gcd ((2^a.val*q^b.val:ℕ):ℤ) (γ 1 0):ℂ)^2/((2^a.val*q^b.val:ℕ):ℂ))) := by sorry
