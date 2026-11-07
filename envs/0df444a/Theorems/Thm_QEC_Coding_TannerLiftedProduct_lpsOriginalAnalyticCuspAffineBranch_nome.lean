-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalAnalyticCuspAffineBranch_nome
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalAnalyticCuspAffineBranch_nome
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T01:26:32.130198+00:00
-- url     : https://prove2.me/theorems/466b71b1-3471-4523-a480-259683ef7749
-- title:
--   Tanner Lifted Product: lps Original Analytic Cusp Affine Branch nome
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Analytic Cusp Affine Branch nome property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalAnalyticCuspLocalization.lean#L154-L164
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalAnalyticCuspLocalization.lean#L154-L164

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerModularEquation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspSeriesReduction
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalAnalyticCuspLocalization
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology
open scoped UpperHalfPlane MatrixGroups
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalAnalyticCuspAffineBranch_nome (m : ℕ) (hm : 0<m) (r : ℚ) (τ : ℍ) :
    lpsOriginalAnalyticCuspLocalizedNomeEval τ (lpsOriginalAnalyticCuspAffineBranch m hm r)=
      lpsOriginalJInvariant (lpsE2AffineMatrix m hm (r:ℝ) • τ) := by sorry
