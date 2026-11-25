-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NormalModelPlace_pointLocalRing_inhabitant_nontrivial_9d8c34c0f10b
-- name    : P2M_GroundTheory_Heights__Heights_NormalModelPlace_pointLocalRing_inhabitant_nontrivial_9d8c34c0f10b
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T13:32:57.921804+00:00
-- url     : https://prove2.me/theorems/fcd73db0-a620-40e3-a1b8-9cf595dca2b6
-- title:
--   P2 M Ground Theory Heights  Heights Normal Model Place point Local Ring inhabitant nontrivial 9d8c34c0f10b: P2 M Ground Theory Heights  Heights Normal Model Place point Local Ring inhabitant nontrivia
-- statement:
--   The P2 M Ground Theory Heights  Heights Normal Model Place point Local Ring inhabitant nontrivial 9d8c34c0f10b construction uses the P2 M Ground Theory Heights  Heights Normal Model Place point Local Ring inhabitant nontrivial 9d8c34c0f10b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StNormalModelPlace.lean#L80-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StNormalModelPlace.lean#L80-L83

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCurveNormalisationLength
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalModel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalModelPlace
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
open MvPolynomial
noncomputable section
variable {σ : Type*}

theorem P2M_GroundTheory_Heights__Heights_NormalModelPlace_pointLocalRing_inhabitant_nontrivial_9d8c34c0f10b :
    Nontrivial (pointLocalRing IndefiniteRowSideFullHecke.ComplexSets.lineDiagonalModel.ideal
      (fun _ ↦ 0 : Fin 1 ⊕ Fin IndefiniteRowSideFullHecke.ComplexSets.lineDiagonalModel.m → ℂ)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NormalModelPlace».«pointLocalRing_inhabitant_nontrivial» := P2M_GroundTheory_Heights__Heights_NormalModelPlace_pointLocalRing_inhabitant_nontrivial_9d8c34c0f10b
