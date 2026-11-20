-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRelativeGaussNormalizationFiberEquiv_root
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalRelativeGaussNormalizationFiberEquiv_root
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T10:31:51.826568+00:00
-- url     : https://prove2.me/theorems/c9cdeee0-4fab-440e-a3de-87a562dff768
-- title:
--   Tanner Lifted Product: lps Original Relative Gauss Normalization Fiber Equiv root
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Relative Gauss Normalization Fiber Equiv root property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRelativeGaussNormalizationBranches.lean#L136-L149
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRelativeGaussNormalizationBranches.lean#L136-L149

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussBranches
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussNormalizationBranches
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalRelativeGaussNormalizationFiberEquiv_root
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    lpsOriginalRelativeGaussNormalizationFiberEquiv N p hNp h4N hN hpN q
      (Ideal.Quotient.mk _ (lpsOriginalRelativeGaussNormalizationRoot N p hNp h4N hN hpN)) =
      ((lpsOriginalGaussMaximalResidueJN N hN p q)^p,
        AdjoinRoot.root ((Polynomial.X : Polynomial (LPSOriginalGaussAffineOrder N hN p ⧸ q))^p -
          Polynomial.C (lpsOriginalGaussMaximalResidueJN N hN p q))) := by sorry
