-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalGaussMaximalResidue_frobenius_finrank
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalGaussMaximalResidue_frobenius_finrank
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T10:57:16.11218+00:00
-- url     : https://prove2.me/theorems/e86a41f5-3ed3-4a89-ab27-7af0f924baf2
-- title:
--   Tanner Lifted Product: lps Original Gauss Maximal Residue frobenius finrank
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Gauss Maximal Residue frobenius finrank property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRelativeGaussFrobeniusDescent.lean#L220-L240
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRelativeGaussFrobeniusDescent.lean#L220-L240

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussSecondBranches
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussFrobeniusDescent
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalGaussMaximalResidue_charP

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalGaussMaximalResidue_frobenius_finrank
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    let K := LPSOriginalGaussAffineOrder N hN p ⧸ q
    letI : Field K := Ideal.Quotient.field q
    letI : CharP K p := lpsOriginalGaussMaximalResidue_charP N hN p q
    letI : Algebra K K := (frobenius K p).toAlgebra
    letI : Module K K := Algebra.toModule
    Module.finrank K K = p := by sorry
