-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_joinCoords_inl_b57b1c2e759e
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_joinCoords_inl_b57b1c2e759e
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T04:11:38.75027+00:00
-- url     : https://prove2.me/theorems/01f13231-e229-4ad5-91c2-989a1eab66c6
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR join Coords inl b57b1c2e759e: P2 M Ground Theory Heights  Heights Numbers DVR join Coords inl b57b1c2e759e
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR join Coords inl b57b1c2e759e construction uses the P2 M Ground Theory Heights  Heights Numbers DVR join Coords inl b57b1c2e759e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PVerticalDivisorJoinPullback.lean#L16-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PVerticalDivisorJoinPullback.lean#L16-L17

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsVerticalDivisorJoinPullback
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Cartier
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PVerticalDivisorJoinPullback
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
variable {K K' : Type} {ι : K → Type} {ι' : K' → Type}

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_joinCoords_inl_b57b1c2e759e {Ω : Type*} [Field Ω] (y : (Σ k, ι k) → Ω) (y' : (Σ k, ι' k) → Ω) (k : K)
    (i : ι k) : joinCoords y y' ⟨Sum.inl k, i⟩ = y ⟨k, i⟩ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«joinCoords_inl» := P2M_GroundTheory_Heights__Heights_NumbersDVR_joinCoords_inl_b57b1c2e759e
