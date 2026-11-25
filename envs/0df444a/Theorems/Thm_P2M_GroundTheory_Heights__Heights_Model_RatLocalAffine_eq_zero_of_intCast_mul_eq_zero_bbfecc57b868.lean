-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_RatLocalAffine_eq_zero_of_intCast_mul_eq_zero_bbfecc57b868
-- name    : P2M_GroundTheory_Heights__Heights_Model_RatLocalAffine_eq_zero_of_intCast_mul_eq_zero_bbfecc57b868
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:30:22.278737+00:00
-- url     : https://prove2.me/theorems/19153818-03b6-4696-b68d-dd9c84b76260
-- title:
--   P2 M Ground Theory Heights  Heights Model Rat Local Affine eq zero of int Cast mul eq zero bbfecc57b868: P2 M Ground Theory Heights  Heights Model Rat Local Affine eq zero of int Cast mul eq zero bbfe
-- statement:
--   The P2 M Ground Theory Heights  Heights Model Rat Local Affine eq zero of int Cast mul eq zero bbfecc57b868 construction uses the P2 M Ground Theory Heights  Heights Model Rat Local Affine eq zero of int Cast mul eq zero bbfecc57b868 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PRatLocalAffine.lean#L13-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PRatLocalAffine.lean#L13-L20

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_RatLocalAffine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PRatLocalAffine
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Model
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
noncomputable section
open GroundTheory.Heights₂.Heights.Model.RatLocalAffine

theorem P2M_GroundTheory_Heights__Heights_Model_RatLocalAffine_eq_zero_of_intCast_mul_eq_zero_bbfecc57b868 {A : Type} [CommRing A] (hA : (Int.castRingHom A).Flat)
    {n : ℤ} (hn : n ≠ 0) {a : A} (h : (n : A) * a = 0) : a = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«RatLocalAffine».«eq_zero_of_intCast_mul_eq_zero» := P2M_GroundTheory_Heights__Heights_Model_RatLocalAffine_eq_zero_of_intCast_mul_eq_zero_bbfecc57b868
