-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_VarietyMassLower_proof_99a791b6e958
-- name    : P2M_GroundTheory_Heights__Heights_VarietyMassLower_proof_99a791b6e958
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T13:41:38.499011+00:00
-- url     : https://prove2.me/theorems/fcbe2f35-f5f4-4ce4-ba8d-9704925cc5bf
-- title:
--   P2 M Ground Theory Heights  Heights Variety Mass Lower proof 99a791b6e958: P2 M Ground Theory Heights  Heights Variety Mass Lower proof 99a791b6e958
-- statement:
--   The P2 M Ground Theory Heights  Heights Variety Mass Lower proof 99a791b6e958 construction uses the P2 M Ground Theory Heights  Heights Variety Mass Lower proof 99a791b6e958 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PVarietyMassLower.lean#L15-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PVarietyMassLower.lean#L15-L65

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StVarietyMassLower
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StTangentGraphLowerDensity
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StVarietyTangentGraphDense
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StVarietyLelongMono
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PVarietyMassLower
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
open MvPolynomial MeasureTheory
open scoped ENNReal
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_VarietyMassLower_proof_99a791b6e958 (hG : VarietyTangentGraphDense.Statement)
    (hL : TangentGraphLowerDensity.Statement) (hM : VarietyLelongMono.Statement) :
    VarietyMassLower.Statement := by sorry

alias «GroundTheory».«Heights₂».«Heights».«VarietyMassLower».«proof» := P2M_GroundTheory_Heights__Heights_VarietyMassLower_proof_99a791b6e958
