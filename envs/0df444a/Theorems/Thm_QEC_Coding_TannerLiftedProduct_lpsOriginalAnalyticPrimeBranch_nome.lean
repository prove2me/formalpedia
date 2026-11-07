-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalAnalyticPrimeBranch_nome
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalAnalyticPrimeBranch_nome
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T02:30:45.818766+00:00
-- url     : https://prove2.me/theorems/5bfd1809-b5a9-4393-abbb-d33175cac280
-- title:
--   Tanner Lifted Product: lps Original Analytic Prime Branch nome
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Analytic Prime Branch nome property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalPrimeCuspCorrespondence.lean#L37-L57
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalPrimeCuspCorrespondence.lean#L37-L57

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPrimeModularBranches
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalAnalyticCuspLocalization
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPrimeCuspCorrespondence
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology
open scoped UpperHalfPlane MatrixGroups
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalAnalyticPrimeBranch_nome (p : ℕ) [Fact p.Prime]
    (i : Option (Fin p)) (τ : ℍ) :
    lpsOriginalAnalyticCuspLocalizedNomeEval τ (lpsOriginalAnalyticPrimeBranch p i)=
      lpsOriginalPrimeBranch p i (lpsE2AffineMatrix p (Fact.out : p.Prime).pos 0 • τ) := by sorry
