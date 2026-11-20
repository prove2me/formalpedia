-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerPolynomial_normalDualRoot
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerPolynomial_normalDualRoot
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T08:58:53.895578+00:00
-- url     : https://prove2.me/theorems/a5f739ac-85b4-41e2-9b5c-ea5aca003e6f
-- title:
--   Tanner Lifted Product: lps Original Integer Polynomial normal Dual Root
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Integer Polynomial normal Dual Root property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegralDualRelation.lean#L78-L105
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegralDualRelation.lean#L78-L105

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPrimeIntegralHeckeRelation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGaussSpecialFiber
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegralDualRelation
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerPolynomial_normalDualRoot
    (N : ℕ) [NeZero N] (hN : 0 < N) :
    (lpsOriginalIntegerPolynomial N hN).eval₂
      (lpsOriginalIntegerFrickeCoefficientMap N hN)
      (lpsOriginalIntegerNormalJ N hN) = 0 := by sorry
