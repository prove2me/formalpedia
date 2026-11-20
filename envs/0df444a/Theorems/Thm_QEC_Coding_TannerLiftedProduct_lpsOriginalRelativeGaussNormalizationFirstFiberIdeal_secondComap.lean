-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRelativeGaussNormalizationFirstFiberIdeal_secondComap
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalRelativeGaussNormalizationFirstFiberIdeal_secondComap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T11:36:29.974846+00:00
-- url     : https://prove2.me/theorems/5b30d2b8-d537-44ac-902f-06eb18823dcd
-- title:
--   Tanner Lifted Product: lps Original Relative Gauss Normalization First Fiber Ideal second Comap
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Relative Gauss Normalization First Fiber Ideal second Comap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRelativeGaussFrobeniusFiber.lean#L201-L209
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRelativeGaussFrobeniusFiber.lean#L201-L209

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussSecondOrderMap
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussFrobeniusFiber
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalRelativeGaussNormalizationFirstFiberIdeal_secondComap
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    (q.map (lpsOriginalRelativeGaussNormalizationCoefficients N p hNp h4N hN hpN)).comap
      (lpsOriginalRelativeGaussNormalizationSecondOrderMap N p hNp h4N hN hpN) = q := by sorry
