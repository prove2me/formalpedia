-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRelativeGaussInseparableBranchFrobeniusEquiv_symm_prime_power
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalRelativeGaussInseparableBranchFrobeniusEquiv_symm_prime_power
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T10:57:07.009271+00:00
-- url     : https://prove2.me/theorems/70cbcdc8-6c3c-45c8-a7b1-1c9125c46d9f
-- title:
--   Tanner Lifted Product: lps Original Relative Gauss Inseparable Branch Frobenius Equiv symm prime power
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Relative Gauss Inseparable Branch Frobenius Equiv symm prime power property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRelativeGaussFrobeniusDescent.lean#L378-L395
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRelativeGaussFrobeniusDescent.lean#L378-L395

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussSecondBranches
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussFrobeniusDescent
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalGaussMaximalResidue_charP

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalRelativeGaussInseparableBranchFrobeniusEquiv_symm_prime_power
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal]
    (u : LPSOriginalGaussAffineOrder N hN p ⧸ q) :
    letI : Field (LPSOriginalGaussAffineOrder N hN p ⧸ q) := Ideal.Quotient.field q
    letI : CharP (LPSOriginalGaussAffineOrder N hN p ⧸ q) p :=
      lpsOriginalGaussMaximalResidue_charP N hN p q
    (lpsOriginalRelativeGaussInseparableBranchFrobeniusEquiv N p hNp h4N hN hpN q).symm
      (u^p) = AdjoinRoot.of ((Polynomial.X : Polynomial (LPSOriginalGaussAffineOrder N hN p ⧸ q))^p -
        Polynomial.C (lpsOriginalGaussMaximalResidueJN N hN p q)) u := by sorry
