-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegralLevelCoefficientEval_complex
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalIntegralLevelCoefficientEval_complex
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T02:24:26.100508+00:00
-- url     : https://prove2.me/theorems/dfc86f6f-f377-43c4-b4fe-321edd0e810e
-- title:
--   Tanner Lifted Product: lps Original Integral Level Coefficient Eval complex
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Integral Level Coefficient Eval complex property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCoprimeModularReduction.lean#L148-L162
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCoprimeModularReduction.lean#L148-L162

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalIntegralLevelCoefficientEval_complex
    (N : ℕ) (hN : 0 < N) :
    (lpsOriginalCuspCoefficientMap (lpsOriginalLevelPhaseRing N).val.toRingHom).comp
      (lpsOriginalIntegralLevelCoefficientEval N hN) =
      lpsOriginalAnalyticCuspLocalizedTaylor.comp
        (lpsOriginalAnalyticLevelCoefficientEval N hN) := by sorry
