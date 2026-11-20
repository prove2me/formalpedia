-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRelativeGaussNormalization_secondResidueAlternatives
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalRelativeGaussNormalization_secondResidueAlternatives
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T10:36:29.893555+00:00
-- url     : https://prove2.me/theorems/a931082c-1571-4751-98ec-f2fb923d91b7
-- title:
--   Tanner Lifted Product: lps Original Relative Gauss Normalization second Residue Alternatives
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Relative Gauss Normalization second Residue Alternatives property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRelativeGaussSecondBranches.lean#L79-L92
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRelativeGaussSecondBranches.lean#L79-L92

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGaussFirstResidueCoordinate
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussSecondCoordinates
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussSecondBranches
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalRelativeGaussNormalization_secondResidueAlternatives
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N)
    (A : Type*) [CommRing A] [IsDomain A] [Algebra (ZMod p) A]
    (f : LPSOriginalRelativeGaussNormalization N p hNp h4N hN →+* A) :
    f (lpsOriginalRelativeGaussNormalizationSecondJ N p hNp h4N hN) =
        (f (lpsOriginalRelativeGaussNormalizationFirstJ N p hNp h4N hN hpN))^p ∨
      (f (lpsOriginalRelativeGaussNormalizationSecondJ N p hNp h4N hN))^p =
        f (lpsOriginalRelativeGaussNormalizationFirstJ N p hNp h4N hN hpN) := by sorry
