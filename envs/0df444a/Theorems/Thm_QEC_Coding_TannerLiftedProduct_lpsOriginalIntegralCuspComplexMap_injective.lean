-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegralCuspComplexMap_injective
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalIntegralCuspComplexMap_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T02:25:19.560079+00:00
-- url     : https://prove2.me/theorems/bfbae43c-cfea-4990-ac82-e085c148ed4d
-- title:
--   Tanner Lifted Product: lps Original Integral Cusp Complex Map injective
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Integral Cusp Complex Map injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCoprimeModularReduction.lean#L170-L174
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCoprimeModularReduction.lean#L170-L174

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalIntegralCuspComplexMap_injective (N : ℕ) :
    Function.Injective (lpsOriginalCuspCoefficientMap (lpsOriginalLevelPhaseRing N).val.toRingHom) := by sorry
