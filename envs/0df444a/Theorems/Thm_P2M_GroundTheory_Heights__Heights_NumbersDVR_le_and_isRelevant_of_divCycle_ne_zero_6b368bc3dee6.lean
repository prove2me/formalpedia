-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_le_and_isRelevant_of_divCycle_ne_zero_6b368bc3dee6
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_le_and_isRelevant_of_divCycle_ne_zero_6b368bc3dee6
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:55:40.794614+00:00
-- url     : https://prove2.me/theorems/5b3c032a-b3c0-4f11-ac06-4be1dee03ca7
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR le and is Relevant of div Cycle ne zero 6b368bc3dee6: P2 M Ground Theory Heights  Heights Numbers DVR le and is Relevant of div Cycle ne zero 6b368bc3de
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR le and is Relevant of div Cycle ne zero 6b368bc3dee6 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR le and is Relevant of div Cycle ne zero 6b368bc3dee6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/Cartier.lean#L101-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/Cartier.lean#L101-L106

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_le_and_isRelevant_of_divCycle_ne_zero_6b368bc3dee6 {P : Ideal (MRing ι R)} {f : MRing ι R}
    {W : Ideal (MRing ι R)} (h : divCycle P f W ≠ 0) : W.IsPrime ∧ P ≤ W ∧ IsRelevant W := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«le_and_isRelevant_of_divCycle_ne_zero» := P2M_GroundTheory_Heights__Heights_NumbersDVR_le_and_isRelevant_of_divCycle_ne_zero_6b368bc3dee6
