-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalAnalyticPrimeJ_nome
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalAnalyticPrimeJ_nome
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T02:30:40.127343+00:00
-- url     : https://prove2.me/theorems/f4cd36ef-cbe8-4eb4-8d6f-5fa7e3af46f1
-- title:
--   Tanner Lifted Product: lps Original Analytic Prime J nome
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Analytic Prime J nome property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalPrimeCuspCorrespondence.lean#L29-L35
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalPrimeCuspCorrespondence.lean#L29-L35

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPrimeModularBranches
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalAnalyticCuspLocalization
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPrimeCuspCorrespondence
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology
open scoped UpperHalfPlane MatrixGroups
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalAnalyticPrimeJ_nome (p : ℕ) [Fact p.Prime] (τ : ℍ) :
    lpsOriginalAnalyticCuspLocalizedNomeEval τ (lpsOriginalAnalyticPrimeJ p)=
      lpsOriginalJInvariant (lpsE2AffineMatrix p (Fact.out : p.Prime).pos 0 • τ) := by sorry
