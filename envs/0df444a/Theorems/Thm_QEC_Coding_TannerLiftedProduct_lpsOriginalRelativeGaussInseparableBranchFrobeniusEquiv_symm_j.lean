-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRelativeGaussInseparableBranchFrobeniusEquiv_symm_j
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalRelativeGaussInseparableBranchFrobeniusEquiv_symm_j
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T10:57:25.909121+00:00
-- url     : https://prove2.me/theorems/a5abda49-b823-4909-b5e2-0c5573e5bb13
-- title:
--   Tanner Lifted Product: lps Original Relative Gauss Inseparable Branch Frobenius Equiv symm j
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Relative Gauss Inseparable Branch Frobenius Equiv symm j property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRelativeGaussFrobeniusDescent.lean#L339-L357
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRelativeGaussFrobeniusDescent.lean#L339-L357

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussSecondBranches
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussFrobeniusDescent
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalGaussMaximalResidue_charP

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalRelativeGaussInseparableBranchFrobeniusEquiv_symm_j
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    letI : Field (LPSOriginalGaussAffineOrder N hN p ⧸ q) := Ideal.Quotient.field q
    letI : CharP (LPSOriginalGaussAffineOrder N hN p ⧸ q) p :=
      lpsOriginalGaussMaximalResidue_charP N hN p q
    (lpsOriginalRelativeGaussInseparableBranchFrobeniusEquiv N p hNp h4N hN hpN q).symm
      (lpsOriginalGaussMaximalResidueJ N hN p q) =
      lpsOriginalRelativeGaussNormalizationInseparableBranchMap N p hNp h4N hN hpN q
        (lpsOriginalRelativeGaussNormalizationSecondJ N p hNp h4N hN) := by sorry
