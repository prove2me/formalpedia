-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRelativeGaussNormalizationInseparableBranchMap_firstJ
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalRelativeGaussNormalizationInseparableBranchMap_firstJ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T10:36:33.140761+00:00
-- url     : https://prove2.me/theorems/078e15d1-9b23-4473-986f-db2f0ca20418
-- title:
--   Tanner Lifted Product: lps Original Relative Gauss Normalization Inseparable Branch Map first J
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Relative Gauss Normalization Inseparable Branch Map first J property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRelativeGaussSecondBranches.lean#L52-L65
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRelativeGaussSecondBranches.lean#L52-L65

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGaussFirstResidueCoordinate
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussSecondCoordinates
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussSecondBranches
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalRelativeGaussNormalizationInseparableBranchMap_firstJ
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    lpsOriginalRelativeGaussNormalizationInseparableBranchMap N p hNp h4N hN hpN q
      (lpsOriginalRelativeGaussNormalizationFirstJ N p hNp h4N hN hpN) =
      AdjoinRoot.of ((Polynomial.X : Polynomial (LPSOriginalGaussAffineOrder N hN p ⧸ q))^p -
        Polynomial.C (lpsOriginalGaussMaximalResidueJN N hN p q))
        (lpsOriginalGaussMaximalResidueJ N hN p q) := by sorry
