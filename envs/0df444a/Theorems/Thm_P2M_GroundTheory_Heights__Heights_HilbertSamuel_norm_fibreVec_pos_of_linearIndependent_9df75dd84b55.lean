-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_norm_fibreVec_pos_of_linearIndependent_9df75dd84b55
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_norm_fibreVec_pos_of_linearIndependent_9df75dd84b55
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:42:24.175468+00:00
-- url     : https://prove2.me/theorems/6010bdf1-eb10-472f-8f7a-9182b3c5a5a0
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel norm fibre Vec pos of linear Independent 9df75dd84b55: P2 M Ground Theory Heights  Heights Hilbert Samuel norm fibre Vec pos of linear Independent 9d
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel norm fibre Vec pos of linear Independent 9df75dd84b55 construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel norm fibre Vec pos of linear Independent 9df75dd84b55 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/NormFibreVecPosOfLinearIndependent.lean#L15-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/NormFibreVecPosOfLinearIndependent.lean#L15-L18

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsLattice
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StandardLatticeVecIndep
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_ShortFamilyEquivSmallFamilyVec
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_NormFibreVecPosOfLinearIndependent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open NumberField TensorProduct
noncomputable section
variable {K : Type} [Field K] [NumberField K]

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_norm_fibreVec_pos_of_linearIndependent_9df75dd84b55 {E : HermitianBundle.{0} K} {ι : Type*}
    {s : ι → E.carrier} (hs : LinearIndependent (𝓞 K) s) (σ : K →+* ℂ) (i : ι) :
    0 < ‖fibreVec E.metric σ (s i)‖ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«norm_fibreVec_pos_of_linearIndependent» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_norm_fibreVec_pos_of_linearIndependent_9df75dd84b55
