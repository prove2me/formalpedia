-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalModPrimeCoefficientEval_reduction
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalModPrimeCoefficientEval_reduction
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T02:31:43.210316+00:00
-- url     : https://prove2.me/theorems/653cee32-43c8-43e7-9ec2-065ee089298e
-- title:
--   Tanner Lifted Product: lps Original Mod Prime Coefficient Eval reduction
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Mod Prime Coefficient Eval reduction property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalPrimeCuspCorrespondence.lean#L191-L202
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalPrimeCuspCorrespondence.lean#L191-L202

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPrimeModularBranches
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalAnalyticCuspLocalization
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPrimeCuspCorrespondence
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology
open scoped UpperHalfPlane MatrixGroups
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalModPrimeCoefficientEval_reduction (p : ℕ) [Fact p.Prime] :
    (lpsOriginalCyclotomicCuspReduction p).comp (lpsOriginalCyclotomicPrimeCoefficientEval p)=
      lpsOriginalModPrimeCoefficientEval p := by sorry
