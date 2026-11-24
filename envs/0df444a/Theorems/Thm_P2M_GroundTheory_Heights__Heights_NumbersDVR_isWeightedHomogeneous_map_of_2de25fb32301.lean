-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_isWeightedHomogeneous_map_of_2de25fb32301
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_isWeightedHomogeneous_map_of_2de25fb32301
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:37:49.695292+00:00
-- url     : https://prove2.me/theorems/e81a6d7e-1662-4f29-a175-77a157957302
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR is Weighted Homogeneous map of 2de25fb32301: P2 M Ground Theory Heights  Heights Numbers DVR is Weighted Homogeneous map of 2de25fb32301
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR is Weighted Homogeneous map of 2de25fb32301 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR is Weighted Homogeneous map of 2de25fb32301 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PSpecialIdealMultiHomog.lean#L13-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PSpecialIdealMultiHomog.lean#L13-L20

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsCN
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSpecialIdealMultiHomog
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
attribute [local instance] MvPolynomial.weightedGradedAlgebra
universe u

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_isWeightedHomogeneous_map_of_2de25fb32301 {σ M R S : Type*} [AddCommMonoid M] [CommRing R]
    [CommRing S] (f : R →+* S) (w : σ → M) {p : MvPolynomial σ R} {b : M}
    (hp : IsWeightedHomogeneous w p b) : IsWeightedHomogeneous w (MvPolynomial.map f p) b := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«isWeightedHomogeneous_map_of» := P2M_GroundTheory_Heights__Heights_NumbersDVR_isWeightedHomogeneous_map_of_2de25fb32301
