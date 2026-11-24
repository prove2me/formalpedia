-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_KLinesQuotIndex_coordProj_surjective_59e6542cb5fd
-- name    : P2M_GroundTheory_Heights__Heights_KLinesQuotIndex_coordProj_surjective_59e6542cb5fd
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:33:07.18738+00:00
-- url     : https://prove2.me/theorems/d5b02a0f-c4c6-4d6d-9d71-7c0e91b001a6
-- title:
--   P2 M Ground Theory Heights  Heights KLines Quot Index coord Proj surjective 59e6542cb5fd: P2 M Ground Theory Heights  Heights KLines Quot Index coord Proj surjective 59e6542cb5fd
-- statement:
--   The P2 M Ground Theory Heights  Heights KLines Quot Index coord Proj surjective 59e6542cb5fd construction uses the P2 M Ground Theory Heights  Heights KLines Quot Index coord Proj surjective 59e6542cb5fd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PLinesQuotIndex.lean#L18-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PLinesQuotIndex.lean#L18-L21

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLines
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PLinesQuotIndex
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open NumberField
open GroundTheory.Heights₂.Heights.KLinesQuotIndex

theorem P2M_GroundTheory_Heights__Heights_KLinesQuotIndex_coordProj_surjective_59e6542cb5fd {K : Type*} [Field K] {n m k : ℕ}
    (B : Module.Basis (Fin m ⊕ Fin k) K (Fin n → K)) : Function.Surjective (coordProj B) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«KLinesQuotIndex».«coordProj_surjective» := P2M_GroundTheory_Heights__Heights_KLinesQuotIndex_coordProj_surjective_59e6542cb5fd
