-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegralLevelCoefficientEval_reduction
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalIntegralLevelCoefficientEval_reduction
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T02:25:20.233214+00:00
-- url     : https://prove2.me/theorems/5e1d5c4a-b36e-45dd-b512-26b5ad76393d
-- title:
--   Tanner Lifted Product: lps Original Integral Level Coefficient Eval reduction
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Integral Level Coefficient Eval reduction property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCoprimeModularReduction.lean#L200-L212
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCoprimeModularReduction.lean#L200-L212

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalIntegralLevelCoefficientEval_reduction
    (N : ℕ) (hN : 0 < N) (p : ℕ) (hp : p.Prime) :
    (lpsOriginalCuspCoefficientMap (Ideal.Quotient.mk (lpsOriginalLevelPhasePrime N hN p hp))).comp
      (lpsOriginalIntegralLevelCoefficientEval N hN) =
      lpsOriginalResidueLevelCoefficientEval N hN p hp := by sorry
