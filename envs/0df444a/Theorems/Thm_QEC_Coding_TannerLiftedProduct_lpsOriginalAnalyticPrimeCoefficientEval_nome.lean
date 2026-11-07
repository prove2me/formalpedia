-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalAnalyticPrimeCoefficientEval_nome
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalAnalyticPrimeCoefficientEval_nome
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T02:30:42.416504+00:00
-- url     : https://prove2.me/theorems/5b53a819-d71c-4105-a005-a85e603aa86b
-- title:
--   Tanner Lifted Product: lps Original Analytic Prime Coefficient Eval nome
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Analytic Prime Coefficient Eval nome property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalPrimeCuspCorrespondence.lean#L64-L72
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalPrimeCuspCorrespondence.lean#L64-L72

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPrimeModularBranches
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalAnalyticCuspLocalization
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPrimeCuspCorrespondence
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology
open scoped UpperHalfPlane MatrixGroups
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalAnalyticPrimeCoefficientEval_nome (p : ℕ) [Fact p.Prime] (τ : ℍ) :
    (lpsOriginalAnalyticCuspLocalizedNomeEval τ).comp
      (lpsOriginalAnalyticPrimeCoefficientEval p)=
    (Polynomial.evalRingHom
      (lpsOriginalJInvariant (lpsE2AffineMatrix p (Fact.out : p.Prime).pos 0 • τ))).comp
      (Polynomial.mapRingHom (Int.castRingHom ℂ)) := by sorry
