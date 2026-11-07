-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalLevelPhaseRing_complexEmbedding_injective
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalLevelPhaseRing_complexEmbedding_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T02:25:13.869194+00:00
-- url     : https://prove2.me/theorems/e88905da-7b16-4216-ad14-889ce4e4df0e
-- title:
--   Tanner Lifted Product: lps Original Level Phase Ring complex Embedding injective
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Level Phase Ring complex Embedding injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCoprimeModularReduction.lean#L165-L168
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCoprimeModularReduction.lean#L165-L168

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalLevelPhaseRing_complexEmbedding_injective (N : ℕ) :
    Function.Injective (lpsOriginalLevelPhaseRing N).val.toRingHom := by sorry
