-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCyclotomicPrimeCoefficientEval_complex
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalCyclotomicPrimeCoefficientEval_complex
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T02:31:41.292857+00:00
-- url     : https://prove2.me/theorems/1667f90b-bca2-48a5-9e1b-4530baeb8ef6
-- title:
--   Tanner Lifted Product: lps Original Cyclotomic Prime Coefficient Eval complex
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Cyclotomic Prime Coefficient Eval complex property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalPrimeCuspCorrespondence.lean#L141-L155
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalPrimeCuspCorrespondence.lean#L141-L155

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPrimeModularBranches
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalAnalyticCuspLocalization
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPrimeCuspCorrespondence
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology
open scoped UpperHalfPlane MatrixGroups
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalCyclotomicPrimeCoefficientEval_complex (p : ℕ) [Fact p.Prime] :
    (lpsOriginalCuspCoefficientMap (lpsOriginalCyclotomicComplexEmbedding p)).comp
      (lpsOriginalCyclotomicPrimeCoefficientEval p)=
    lpsOriginalAnalyticCuspLocalizedTaylor.comp (lpsOriginalAnalyticPrimeCoefficientEval p) := by sorry
