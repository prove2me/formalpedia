-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRelativeGaussNormalizationFrickePullback_comp_second
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalRelativeGaussNormalizationFrickePullback_comp_second
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T11:40:07.88034+00:00
-- url     : https://prove2.me/theorems/1e8ea106-13aa-40f5-b297-3e8397dfa86e
-- title:
--   Tanner Lifted Product: lps Original Relative Gauss Normalization Fricke Pullback comp second
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Relative Gauss Normalization Fricke Pullback comp second property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRelativeGaussFricke.lean#L182-L200
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRelativeGaussFricke.lean#L182-L200

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGaussFricke
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussSecondResidueDegrees
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussFricke
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalRelativeGaussNormalizationFrickePullback_comp_second
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N) :
    (lpsOriginalRelativeGaussNormalizationFrickePullback N p hNp h4N hN hpN).comp
      (lpsOriginalRelativeGaussNormalizationSecondOrderMap N p hNp h4N hN hpN) =
        (lpsOriginalRelativeGaussNormalizationCoefficients N p hNp h4N hN hpN).comp
          (lpsOriginalGaussFrickeOrderMap N hN p hpN) := by sorry
