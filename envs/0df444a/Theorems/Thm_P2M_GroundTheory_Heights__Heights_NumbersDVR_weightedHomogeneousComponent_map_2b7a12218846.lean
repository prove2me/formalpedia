-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_weightedHomogeneousComponent_map_2b7a12218846
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_weightedHomogeneousComponent_map_2b7a12218846
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T04:12:17.067117+00:00
-- url     : https://prove2.me/theorems/a9b961f9-d87d-4bc5-8ee5-db72da4b73d8
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR weighted Homogeneous Component map 2b7a12218846: P2 M Ground Theory Heights  Heights Numbers DVR weighted Homogeneous Component map 2b7a12218846
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR weighted Homogeneous Component map 2b7a12218846 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR weighted Homogeneous Component map 2b7a12218846 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PGenericFibProps.lean#L13-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PGenericFibProps.lean#L13-L21

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsMultiHomogIdealSpanSingleton
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PGenericFibProps
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
noncomputable section
universe u

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_weightedHomogeneousComponent_map_2b7a12218846 {σ M R S : Type*} [AddCommMonoid M] [CommRing R]
    [CommRing S] (φ : R →+* S) (w : σ → M) (n : M) (p : MvPolynomial σ R) :
    weightedHomogeneousComponent w n (MvPolynomial.map φ p) =
      MvPolynomial.map φ (weightedHomogeneousComponent w n p) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«weightedHomogeneousComponent_map» := P2M_GroundTheory_Heights__Heights_NumbersDVR_weightedHomogeneousComponent_map_2b7a12218846
