-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_joinForm_mem_pointIdeal_iff_ec545b5ede48
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_joinForm_mem_pointIdeal_iff_ec545b5ede48
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:37:47.215454+00:00
-- url     : https://prove2.me/theorems/bd8d67ca-88c1-468b-9cc7-bcd2959a12c4
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR join Form mem point Ideal iff ec545b5ede48: P2 M Ground Theory Heights  Heights Numbers DVR join Form mem point Ideal iff ec545b5ede48
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR join Form mem point Ideal iff ec545b5ede48 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR join Form mem point Ideal iff ec545b5ede48 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PVerticalDivisorJoinPullback.lean#L31-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PVerticalDivisorJoinPullback.lean#L31-L35

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_joinForm_mem_pointIdeal_iff_ec545b5ede48 {Ω : Type*} [Field Ω] (R : Type*) [CommRing R] [Algebra R Ω]
    (y : (Σ k, ι k) → Ω) (y' : (Σ k, ι' k) → Ω) (f : MRing ι R) :
    joinForm f ∈ pointIdeal R (joinCoords y y') ↔ f ∈ pointIdeal R y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«joinForm_mem_pointIdeal_iff» := P2M_GroundTheory_Heights__Heights_NumbersDVR_joinForm_mem_pointIdeal_iff_ec545b5ede48
