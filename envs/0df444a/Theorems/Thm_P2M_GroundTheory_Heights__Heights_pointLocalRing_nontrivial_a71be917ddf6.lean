-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_pointLocalRing_nontrivial_a71be917ddf6
-- name    : P2M_GroundTheory_Heights__Heights_pointLocalRing_nontrivial_a71be917ddf6
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T04:49:28.97245+00:00
-- url     : https://prove2.me/theorems/f51fd74b-86a6-49ae-bc0d-4f1a6f9851c1
-- title:
--   P2 M Ground Theory Heights  Heights point Local Ring nontrivial a71be917ddf6: P2 M Ground Theory Heights  Heights point Local Ring nontrivial a71be917ddf6
-- statement:
--   The P2 M Ground Theory Heights  Heights point Local Ring nontrivial a71be917ddf6 construction uses the P2 M Ground Theory Heights  Heights point Local Ring nontrivial a71be917ddf6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StNormalModelPlace.lean#L37-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StNormalModelPlace.lean#L37-L49

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

theorem P2M_GroundTheory_Heights__Heights_pointLocalRing_nontrivial_a71be917ddf6 (I : Ideal (MvPolynomial σ ℂ)) (w : σ → ℂ)
    (hw : w ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn I) : Nontrivial (pointLocalRing I w) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«pointLocalRing_nontrivial» := P2M_GroundTheory_Heights__Heights_pointLocalRing_nontrivial_a71be917ddf6
