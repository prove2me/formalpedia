-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCyclotomicComplexRoot_phase
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalCyclotomicComplexRoot_phase
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T02:31:59.483749+00:00
-- url     : https://prove2.me/theorems/e4f1d485-7ffe-4ca4-8d80-3f5c5ffd5cdd
-- title:
--   Tanner Lifted Product: lps Original Cyclotomic Complex Root phase
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Cyclotomic Complex Root phase property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalPrimeCuspCorrespondence.lean#L107-L113
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalPrimeCuspCorrespondence.lean#L107-L113

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPrimeModularBranches
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalAnalyticCuspLocalization
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPrimeCuspCorrespondence
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology
open scoped UpperHalfPlane MatrixGroups
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalCyclotomicComplexRoot_phase (p : ℕ) [Fact p.Prime] (m : ℕ) :
    (lpsOriginalCyclotomicComplexRoot p)^m=
      Function.Periodic.qParam 1 (((((m:ℚ)/(p:ℚ)):ℚ)):ℂ) := by sorry
