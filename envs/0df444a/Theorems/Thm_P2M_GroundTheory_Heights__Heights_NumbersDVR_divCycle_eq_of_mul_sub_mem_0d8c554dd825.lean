-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_divCycle_eq_of_mul_sub_mem_0d8c554dd825
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_divCycle_eq_of_mul_sub_mem_0d8c554dd825
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T00:57:01.1678+00:00
-- url     : https://prove2.me/theorems/fb3bbf47-d2b5-4a7a-96c5-0ef10cad0c1a
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR div Cycle eq of mul sub mem 0d8c554dd825: P2 M Ground Theory Heights  Heights Numbers DVR div Cycle eq of mul sub mem 0d8c554dd825
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR div Cycle eq of mul sub mem 0d8c554dd825 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR div Cycle eq of mul sub mem 0d8c554dd825 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/Cartier.lean#L70-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/Cartier.lean#L70-L99

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Cartier
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
variable {K : Type*} {ι : K → Type*} {R : Type*} [CommRing R]

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_divCycle_eq_of_mul_sub_mem_0d8c554dd825 {P : Ideal (MRing ι R)} {f g u v : MRing ι R}
    {W : Ideal (MRing ι R)} (hu : u ∉ W) (hv : v ∉ W) (h : u * f - v * g ∈ P) :
    divCycle P f W = divCycle P g W := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«divCycle_eq_of_mul_sub_mem» := P2M_GroundTheory_Heights__Heights_NumbersDVR_divCycle_eq_of_mul_sub_mem_0d8c554dd825
