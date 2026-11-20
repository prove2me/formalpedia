-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRelativeGaussNormalization_secondPrimeRoot
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalRelativeGaussNormalization_secondPrimeRoot
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T10:36:30.016248+00:00
-- url     : https://prove2.me/theorems/d5133647-c0e2-4d69-93f6-dd0f21a0b169
-- title:
--   Tanner Lifted Product: lps Original Relative Gauss Normalization second Prime Root
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Relative Gauss Normalization second Prime Root property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRelativeGaussSecondCoordinates.lean#L185-L215
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRelativeGaussSecondCoordinates.lean#L185-L215

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussNormalizationBranches
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalSecondIntegerHecke
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussSecondCoordinates
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalRelativeGaussNormalization_secondPrimeRoot
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N) :
    (lpsOriginalIntegerPolynomial p (Fact.out : p.Prime).pos).eval₂
      (Polynomial.eval₂RingHom (Int.castRingHom _)
        (lpsOriginalRelativeGaussNormalizationFirstJ N p hNp h4N hN hpN))
      (lpsOriginalRelativeGaussNormalizationSecondJ N p hNp h4N hN) = 0 := by sorry
