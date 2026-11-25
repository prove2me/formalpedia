-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NormalModelPointOfPlace_proof_decb66a93671
-- name    : P2M_GroundTheory_Heights__Heights_NormalModelPointOfPlace_proof_decb66a93671
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T13:33:33.702866+00:00
-- url     : https://prove2.me/theorems/92e6869e-c41a-48d5-8738-a6de08286d3a
-- title:
--   P2 M Ground Theory Heights  Heights Normal Model Point Of Place proof decb66a93671: P2 M Ground Theory Heights  Heights Normal Model Point Of Place proof decb66a93671
-- statement:
--   The P2 M Ground Theory Heights  Heights Normal Model Point Of Place proof decb66a93671 construction uses the P2 M Ground Theory Heights  Heights Normal Model Point Of Place proof decb66a93671 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PNormalModelPointOfPlace.lean#L14-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PNormalModelPointOfPlace.lean#L14-L47

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalModelPointOfPlace
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StModelLocalizationMaximalPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLocalizationAtPrimeQuotient
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChartLocalOrder
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PNormalModelPointOfPlace
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartLocalOrder_proof_c02df12483c9
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowFormSection_proof_5b1b05e34c1e

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial ComplexSets
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_NormalModelPointOfPlace_proof_decb66a93671 (hLoc : NormalisationModelLocalization.Statement)
    (hMax : ModelLocalizationMaximalPoint.Statement) (hAt : LocalizationAtPrimeQuotient.Statement.{0}) :
    NormalModelPointOfPlace.Statement := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NormalModelPointOfPlace».«proof» := P2M_GroundTheory_Heights__Heights_NormalModelPointOfPlace_proof_decb66a93671
