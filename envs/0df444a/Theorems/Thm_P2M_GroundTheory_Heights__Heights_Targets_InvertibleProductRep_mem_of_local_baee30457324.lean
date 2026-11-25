-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_InvertibleProductRep_mem_of_local_baee30457324
-- name    : P2M_GroundTheory_Heights__Heights_Targets_InvertibleProductRep_mem_of_local_baee30457324
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T04:40:24.804629+00:00
-- url     : https://prove2.me/theorems/319642c9-c904-4d10-9278-41aaeb9b8e7d
-- title:
--   P2 M Ground Theory Heights  Heights Targets Invertible Product Rep mem of local baee30457324: P2 M Ground Theory Heights  Heights Targets Invertible Product Rep mem of local baee30457324
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets Invertible Product Rep mem of local baee30457324 construction uses the P2 M Ground Theory Heights  Heights Targets Invertible Product Rep mem of local baee30457324 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PInvertibleProductRep.lean#L7-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PInvertibleProductRep.lean#L7-L33

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsInvertibleIndexMulSteps
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PInvertibleProductRep
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets

theorem P2M_GroundTheory_Heights__Heights_Targets_InvertibleProductRep_mem_of_local_baee30457324 {Ω : Type} [Field Ω] (B : Subring Ω) (Y : AddSubgroup Ω)
    (hY : ∀ b ∈ B, ∀ z ∈ Y, b * z ∈ Y) (z : Ω)
    (hz : ∀ m : Ideal B, m.IsMaximal → ∃ b : B, b ∉ m ∧ (b : Ω) * z ∈ Y) : z ∈ Y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«InvertibleProductRep».«mem_of_local» := P2M_GroundTheory_Heights__Heights_Targets_InvertibleProductRep_mem_of_local_baee30457324
