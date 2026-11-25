-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_pointLocalRing_exists_mul_mem_11beafa9d30c
-- name    : P2M_GroundTheory_Heights__Heights_pointLocalRing_exists_mul_mem_11beafa9d30c
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T04:49:40.693809+00:00
-- url     : https://prove2.me/theorems/32a9c722-a440-4967-8ecc-c9c32fd3b966
-- title:
--   P2 M Ground Theory Heights  Heights point Local Ring exists mul mem 11beafa9d30c: P2 M Ground Theory Heights  Heights point Local Ring exists mul mem 11beafa9d30c
-- statement:
--   The P2 M Ground Theory Heights  Heights point Local Ring exists mul mem 11beafa9d30c construction uses the P2 M Ground Theory Heights  Heights point Local Ring exists mul mem 11beafa9d30c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PointLocalRingOrder.lean#L26-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PointLocalRingOrder.lean#L26-L38

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

theorem P2M_GroundTheory_Heights__Heights_pointLocalRing_exists_mul_mem_11beafa9d30c (I : Ideal (MvPolynomial σ ℂ)) (w : σ → ℂ) (g : MvPolynomial σ ℂ)
    (hg : algebraMap (MvPolynomial σ ℂ) (pointLocalRing I w) g = 0) :
    ∃ s : MvPolynomial σ ℂ, eval w s ≠ 0 ∧ s * g ∈ I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«pointLocalRing_exists_mul_mem» := P2M_GroundTheory_Heights__Heights_pointLocalRing_exists_mul_mem_11beafa9d30c
