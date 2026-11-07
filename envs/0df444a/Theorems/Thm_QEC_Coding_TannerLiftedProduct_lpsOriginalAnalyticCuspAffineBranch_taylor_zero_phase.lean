-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalAnalyticCuspAffineBranch_taylor_zero_phase
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalAnalyticCuspAffineBranch_taylor_zero_phase
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T01:25:41.457966+00:00
-- url     : https://prove2.me/theorems/62db34a3-44e2-45c3-b065-18b66be36bc3
-- title:
--   Tanner Lifted Product: lps Original Analytic Cusp Affine Branch taylor zero phase
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Analytic Cusp Affine Branch taylor zero phase property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalAnalyticCuspLocalization.lean#L187-L199
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalAnalyticCuspLocalization.lean#L187-L199

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerModularEquation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspSeriesReduction
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalAnalyticCuspLocalization
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology
open scoped UpperHalfPlane MatrixGroups
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalAnalyticCuspAffineBranch_taylor_zero_phase (m : ℕ) (hm : 0<m) :
    lpsOriginalAnalyticCuspLocalizedTaylor (lpsOriginalAnalyticCuspAffineBranch m hm 0)=
      lpsOriginalCuspJWidth ℂ m hm.ne' := by sorry
