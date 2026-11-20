-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRelativeGaussNormalizationFiberFrobeniusRingEquiv_comp_second
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalRelativeGaussNormalizationFiberFrobeniusRingEquiv_comp_second
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T11:36:22.669832+00:00
-- url     : https://prove2.me/theorems/4bf4af63-b5fc-4244-843f-46ab0e2c1873
-- title:
--   Tanner Lifted Product: lps Original Relative Gauss Normalization Fiber Frobenius Ring Equiv comp second
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Relative Gauss Normalization Fiber Frobenius Ring Equiv comp second property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRelativeGaussFrobeniusFiber.lean#L179-L199
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRelativeGaussFrobeniusFiber.lean#L179-L199

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussSecondOrderMap
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussFrobeniusFiber
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalGaussMaximalResidue_charP

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalRelativeGaussNormalizationFiberFrobeniusRingEquiv_comp_second
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    let K := LPSOriginalGaussAffineOrder N hN p ⧸ q
    letI : Field K := Ideal.Quotient.field q
    letI : CharP K p := lpsOriginalGaussMaximalResidue_charP N hN p q
    (lpsOriginalRelativeGaussNormalizationFiberFrobeniusRingEquiv N p hNp h4N hN hpN q).toRingHom.comp
      (lpsOriginalRelativeGaussNormalizationSecondFiberMap N p hNp h4N hN hpN q) =
        (frobenius K p).prod (RingHom.id K) := by sorry
