-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_mem_of_divCycle_ne_zero_c222af189275
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_mem_of_divCycle_ne_zero_c222af189275
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T13:33:30.419861+00:00
-- url     : https://prove2.me/theorems/5ed37056-9607-4a6b-ba2f-549699d5cf02
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR mem of div Cycle ne zero c222af189275: P2 M Ground Theory Heights  Heights Numbers DVR mem of div Cycle ne zero c222af189275
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR mem of div Cycle ne zero c222af189275 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR mem of div Cycle ne zero c222af189275 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/StatementsSegreClosureNumber.lean#L74-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/StatementsSegreClosureNumber.lean#L74-L80

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsSegreClosureModel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsSegreClosureNumber
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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_mem_of_divCycle_ne_zero_c222af189275 {K : Type*} {ι : K → Type*} {R : Type*} [CommRing R]
    {P : Ideal (MRing ι R)} {f : MRing ι R} {W : Ideal (MRing ι R)} (h : divCycle P f W ≠ 0) :
    f ∈ W ∧ W.IsPrime ∧ IsRelevant W := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«mem_of_divCycle_ne_zero» := P2M_GroundTheory_Heights__Heights_NumbersDVR_mem_of_divCycle_ne_zero_c222af189275
