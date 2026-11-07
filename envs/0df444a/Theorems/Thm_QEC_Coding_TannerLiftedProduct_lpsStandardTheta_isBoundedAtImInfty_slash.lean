-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsStandardTheta_isBoundedAtImInfty_slash
-- name    : QEC.Coding.TannerLiftedProduct.lpsStandardTheta_isBoundedAtImInfty_slash
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-07T00:19:57.73621+00:00
-- url     : https://prove2.me/theorems/54ebd7e4-73c5-44e6-a407-e80bb35aed94
-- title:
--   Tanner Lifted Product: lps Standard Theta is Bounded At Im Infty slash
-- statement:
--   Every actual rational-cusp slash is bounded along the complete imaginary-part filter.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaCusps.lean#L242-L245
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaCusps.lean#L242-L245

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCharacteristics
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCusps
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm
open scoped MatrixGroups ModularForm

theorem QEC.Coding.TannerLiftedProduct.lpsStandardTheta_isBoundedAtImInfty_slash (q : ℕ) (hq : 0<q) (γ : SL(2,ℤ)) :
    UpperHalfPlane.IsBoundedAtImInfty ((fun w : UpperHalfPlane => lpsStandardTheta q w) ∣[(2:ℤ)] γ) := by sorry
