-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalAnalyticCuspNome_zero_germ
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalAnalyticCuspNome_zero_germ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T01:27:20.000361+00:00
-- url     : https://prove2.me/theorems/84a91a6e-cb68-4379-aa92-ee629c1609c3
-- title:
--   Tanner Lifted Product: lps Original Analytic Cusp Nome zero germ
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Analytic Cusp Nome zero germ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalAnalyticCuspLocalization.lean#L66-L87
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalAnalyticCuspLocalization.lean#L66-L87

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerModularEquation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspSeriesReduction
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalAnalyticCuspLocalization
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology
open scoped UpperHalfPlane MatrixGroups
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalAnalyticCuspNome_zero_germ (F : lpsOriginalCuspAnalyticSubring)
    (hF : ∀ τ : ℍ,F.val (Function.Periodic.qParam 1 (τ:ℂ))=0) :
    F.val=ᶠ[𝓝 (0:ℂ)]0 := by sorry
