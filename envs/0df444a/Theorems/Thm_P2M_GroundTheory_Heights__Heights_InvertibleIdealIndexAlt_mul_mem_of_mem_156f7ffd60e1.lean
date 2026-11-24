-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_InvertibleIdealIndexAlt_mul_mem_of_mem_156f7ffd60e1
-- name    : P2M_GroundTheory_Heights__Heights_InvertibleIdealIndexAlt_mul_mem_of_mem_156f7ffd60e1
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:29:22.990727+00:00
-- url     : https://prove2.me/theorems/16f6300d-4873-4e9f-b30c-057de299a197
-- title:
--   P2 M Ground Theory Heights  Heights Invertible Ideal Index Alt mul mem of mem 156f7ffd60e1: P2 M Ground Theory Heights  Heights Invertible Ideal Index Alt mul mem of mem 156f7ffd60e1
-- statement:
--   The P2 M Ground Theory Heights  Heights Invertible Ideal Index Alt mul mem of mem 156f7ffd60e1 construction uses the P2 M Ground Theory Heights  Heights Invertible Ideal Index Alt mul mem of mem 156f7ffd60e1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PInvertibleIdealIndex.lean#L79-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PInvertibleIdealIndex.lean#L79-L81

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsInvertibleIdealIndex
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsOrderIdealIndexExtension
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLocallyPrincipalCoprime
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ExistsSmulMemOfSpanEqTop
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PLinesLineDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PInvertibleIdealIndex
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
noncomputable section
open GroundTheory.Heights₂.Heights.InvertibleIdealIndexAlt
variable {L : Type} [Field L]

theorem P2M_GroundTheory_Heights__Heights_InvertibleIdealIndexAlt_mul_mem_of_mem_156f7ffd60e1 [NumberField L] {B : Subring L} [Module.Finite ℤ B] {S : Submodule (𝓞 L) L} {b z : L}
    (hb : b ∈ B) (hz : z ∈ S) : b * z ∈ S := by sorry

alias «GroundTheory».«Heights₂».«Heights».«InvertibleIdealIndexAlt».«mul_mem_of_mem» := P2M_GroundTheory_Heights__Heights_InvertibleIdealIndexAlt_mul_mem_of_mem_156f7ffd60e1
