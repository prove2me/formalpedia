-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_pointLocalRing_subsingleton_b598c07e40ac
-- name    : P2M_GroundTheory_Heights__Heights_pointLocalRing_subsingleton_b598c07e40ac
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T13:43:16.567687+00:00
-- url     : https://prove2.me/theorems/82c77b97-5484-5a41-88bc-447f66227507
-- title:
--   P2 M Ground Theory Heights  Heights point Local Ring subsingleton b598c07e40ac: P2 M Ground Theory Heights  Heights point Local Ring subsingleton b598c07e40ac
-- statement:
--   The P2 M Ground Theory Heights  Heights point Local Ring subsingleton b598c07e40ac construction uses the P2 M Ground Theory Heights  Heights point Local Ring subsingleton b598c07e40ac property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StNormalModelPlace.lean#L51-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StNormalModelPlace.lean#L51-L59

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

theorem P2M_GroundTheory_Heights__Heights_pointLocalRing_subsingleton_b598c07e40ac (I : Ideal (MvPolynomial σ ℂ)) (w : σ → ℂ)
    (hw : w ∉ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn I) : Subsingleton (pointLocalRing I w) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«pointLocalRing_subsingleton» := P2M_GroundTheory_Heights__Heights_pointLocalRing_subsingleton_b598c07e40ac
