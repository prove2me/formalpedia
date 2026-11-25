-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_pointLocalRing_exists_mul_eq_04799598eeba
-- name    : P2M_GroundTheory_Heights__Heights_pointLocalRing_exists_mul_eq_04799598eeba
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T04:49:45.762811+00:00
-- url     : https://prove2.me/theorems/143525eb-77e7-4567-8094-cb3be4bb326f
-- title:
--   P2 M Ground Theory Heights  Heights point Local Ring exists mul eq 04799598eeba: P2 M Ground Theory Heights  Heights point Local Ring exists mul eq 04799598eeba
-- statement:
--   The P2 M Ground Theory Heights  Heights point Local Ring exists mul eq 04799598eeba construction uses the P2 M Ground Theory Heights  Heights point Local Ring exists mul eq 04799598eeba property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PointLocalRingOrder.lean#L13-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PointLocalRingOrder.lean#L13-L24

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalModelPlace
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PointLocalRingOrder
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
open MvPolynomial Topology
noncomputable section
variable {σ : Type*}

theorem P2M_GroundTheory_Heights__Heights_pointLocalRing_exists_mul_eq_04799598eeba (I : Ideal (MvPolynomial σ ℂ)) (w : σ → ℂ) (x : pointLocalRing I w) :
    ∃ a s : MvPolynomial σ ℂ, eval w s ≠ 0 ∧
      x * algebraMap (MvPolynomial σ ℂ) (pointLocalRing I w) s = algebraMap (MvPolynomial σ ℂ) (pointLocalRing I w) a := by sorry

alias «GroundTheory».«Heights₂».«Heights».«pointLocalRing_exists_mul_eq» := P2M_GroundTheory_Heights__Heights_pointLocalRing_exists_mul_eq_04799598eeba
