-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalAdjoinRootPrimePowerFrobeniusDescent_pow
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalAdjoinRootPrimePowerFrobeniusDescent_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T10:56:42.258532+00:00
-- url     : https://prove2.me/theorems/ee6deec2-a5fe-4555-ad9a-11d056b93426
-- title:
--   Tanner Lifted Product: lps Original Adjoin Root Prime Power Frobenius Descent pow
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Adjoin Root Prime Power Frobenius Descent pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRelativeGaussFrobeniusDescent.lean#L41-L69
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRelativeGaussFrobeniusDescent.lean#L41-L69

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussSecondBranches
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussFrobeniusDescent
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalAdjoinRootPrimePowerFrobeniusDescent_pow
    {K : Type*} [Field K] (p : ℕ) [Fact p.Prime] [CharP K p] (a : K)
    [Fact (Irreducible ((Polynomial.X : Polynomial K)^p - Polynomial.C a))]
    (x : AdjoinRoot ((Polynomial.X : Polynomial K)^p - Polynomial.C a)) :
    AdjoinRoot.of ((Polynomial.X : Polynomial K)^p - Polynomial.C a)
      (lpsOriginalAdjoinRootPrimePowerFrobeniusDescent p a x) = x^p := by sorry
