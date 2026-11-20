-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRelativeGaussNormalizationFirstFiberMap_mk
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalRelativeGaussNormalizationFirstFiberMap_mk
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T11:37:12.695966+00:00
-- url     : https://prove2.me/theorems/7b7ba02d-519a-4b79-bb81-1ba471ac355a
-- title:
--   Tanner Lifted Product: lps Original Relative Gauss Normalization First Fiber Map mk
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Relative Gauss Normalization First Fiber Map mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRelativeGaussFrobeniusFiber.lean#L129-L136
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRelativeGaussFrobeniusFiber.lean#L129-L136

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussSecondOrderMap
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussFrobeniusFiber
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalRelativeGaussNormalizationFirstFiberMap_mk
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal]
    (c : LPSOriginalGaussAffineOrder N hN p) :
    lpsOriginalRelativeGaussNormalizationFirstFiberMap N p hNp h4N hN hpN q (Ideal.Quotient.mk q c) =
      Ideal.Quotient.mk _ (lpsOriginalRelativeGaussNormalizationCoefficients N p hNp h4N hN hpN c) := by sorry
