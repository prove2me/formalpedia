-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_pointConeMap_joinCoords_joinForm_b2442480fdad
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_pointConeMap_joinCoords_joinForm_b2442480fdad
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T04:12:24.108697+00:00
-- url     : https://prove2.me/theorems/5f9e6f0f-8655-4401-b28f-7ed29c936341
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR point Cone Map join Coords join Form b2442480fdad: P2 M Ground Theory Heights  Heights Numbers DVR point Cone Map join Coords join Form b2442480fdad
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR point Cone Map join Coords join Form b2442480fdad construction uses the P2 M Ground Theory Heights  Heights Numbers DVR point Cone Map join Coords join Form b2442480fdad property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PVerticalDivisorJoinPullback.lean#L19-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PVerticalDivisorJoinPullback.lean#L19-L29

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_pointConeMap_joinCoords_joinForm_b2442480fdad {Ω : Type*} [Field Ω] (R : Type*) [CommRing R]
    [Algebra R Ω] (y : (Σ k, ι k) → Ω) (y' : (Σ k, ι' k) → Ω) (f : MRing ι R) :
    pointConeMap R (joinCoords y y') (joinForm f) =
      rename (Sum.inl : K → K ⊕ K') (pointConeMap R y f) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«pointConeMap_joinCoords_joinForm» := P2M_GroundTheory_Heights__Heights_NumbersDVR_pointConeMap_joinCoords_joinForm_b2442480fdad
