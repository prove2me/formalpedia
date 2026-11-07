-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFieldLevelJPolynomialEval_injective
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalFieldLevelJPolynomialEval_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T02:24:28.0102+00:00
-- url     : https://prove2.me/theorems/b5458992-5df4-43bc-bc94-e2bbabdeb3d4
-- title:
--   Tanner Lifted Product: lps Original Field Level JPolynomial Eval injective
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Field Level JPolynomial Eval injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCoprimeModularReduction.lean#L243-L254
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCoprimeModularReduction.lean#L243-L254

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerAffineModel
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCosetCuspSeries
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalAnalyticCuspLocalization
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCoprimeModularReduction
set_option autoImplicit false
open Filter Topology
open scoped UpperHalfPlane MatrixGroups
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
attribute [local instance] lpsOriginalLevelPhasePrime_isMaximal
attribute [local instance] lpsOriginalLevelPhaseResidue_field
attribute [local instance] QEC.Coding.TannerLiftedProduct.lpsOriginalFieldCuspSeries_domain

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalFieldLevelJPolynomialEval_injective
    (K : Type*) [Field K] (N : ℕ) (hN : 0 < N) :
    Function.Injective (lpsOriginalFieldLevelJPolynomialEval K N hN) := by sorry
