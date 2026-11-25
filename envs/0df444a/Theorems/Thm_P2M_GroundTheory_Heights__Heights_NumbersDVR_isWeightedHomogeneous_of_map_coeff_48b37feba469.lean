-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_isWeightedHomogeneous_of_map_coeff_48b37feba469
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_isWeightedHomogeneous_of_map_coeff_48b37feba469
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T04:13:26.62333+00:00
-- url     : https://prove2.me/theorems/a22247a7-6e12-5c54-801c-97230c5f93a4
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR is Weighted Homogeneous of map coeff 48b37feba469: P2 M Ground Theory Heights  Heights Numbers DVR is Weighted Homogeneous of map coeff 48b37feba469
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR is Weighted Homogeneous of map coeff 48b37feba469 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR is Weighted Homogeneous of map coeff 48b37feba469 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PGenericPieceRank.lean#L24-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PGenericPieceRank.lean#L24-L31

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsCN
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PGenericPieceRank
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
variable {O : Type*} [CommRing O] [IsDomain O] {K : Type*} [DecidableEq K] {ι : K → Type*}

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_isWeightedHomogeneous_of_map_coeff_48b37feba469 {R S σ M : Type*} [CommSemiring R] [CommSemiring S]
    [AddCommMonoid M] (f : R →+* S) (hf : Function.Injective f) {w : σ → M}
    {g : MvPolynomial σ R} {b : M} (h : IsWeightedHomogeneous w (map f g) b) :
    IsWeightedHomogeneous w g b := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«isWeightedHomogeneous_of_map_coeff» := P2M_GroundTheory_Heights__Heights_NumbersDVR_isWeightedHomogeneous_of_map_coeff_48b37feba469
