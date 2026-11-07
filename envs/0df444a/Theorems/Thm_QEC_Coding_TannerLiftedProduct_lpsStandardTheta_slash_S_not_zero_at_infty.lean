-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsStandardTheta_slash_S_not_zero_at_infty
-- name    : QEC.Coding.TannerLiftedProduct.lpsStandardTheta_slash_S_not_zero_at_infty
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T21:40:57.607446+00:00
-- url     : https://prove2.me/theorems/4d9d1a1f-2931-43c7-80ae-dd5fa5002f22
-- title:
--   Tanner Lifted Product: lps Standard Theta slash S not zero at infty
-- statement:
--   The Tanner Lifted Product construction uses the lps Standard Theta slash S not zero at infty property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaS.lean#L167-L173
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaS.lean#L167-L173

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSAnalyticTheta
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.ModularForms.Identities
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaS
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm

theorem QEC.Coding.TannerLiftedProduct.lpsStandardTheta_slash_S_not_zero_at_infty (q : ℕ) (hq : 0 < q) :
    ¬ UpperHalfPlane.IsZeroAtImInfty
      ((fun w : UpperHalfPlane => lpsStandardTheta q w) ∣[(2 : ℤ)] ModularGroup.S) := by sorry
