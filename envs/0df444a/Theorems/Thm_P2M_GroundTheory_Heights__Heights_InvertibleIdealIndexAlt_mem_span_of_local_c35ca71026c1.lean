-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_InvertibleIdealIndexAlt_mem_span_of_local_c35ca71026c1
-- name    : P2M_GroundTheory_Heights__Heights_InvertibleIdealIndexAlt_mem_span_of_local_c35ca71026c1
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:26:52.273615+00:00
-- url     : https://prove2.me/theorems/53dd56f2-f043-4c0d-980a-670238956020
-- title:
--   P2 M Ground Theory Heights  Heights Invertible Ideal Index Alt mem span of local c35ca71026c1: P2 M Ground Theory Heights  Heights Invertible Ideal Index Alt mem span of local c35ca71026c1
-- statement:
--   The P2 M Ground Theory Heights  Heights Invertible Ideal Index Alt mem span of local c35ca71026c1 construction uses the P2 M Ground Theory Heights  Heights Invertible Ideal Index Alt mem span of local c35ca71026c1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PInvertibleIdealIndex.lean#L88-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PInvertibleIdealIndex.lean#L88-L120

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

theorem P2M_GroundTheory_Heights__Heights_InvertibleIdealIndexAlt_mem_span_of_local_c35ca71026c1 [NumberField L] {B : Subring L} [Module.Finite ℤ B] {M : AddSubgroup L} {ι : Type}
    {a : ι → L}
    (hloc : ∀ m : Ideal B, m.IsMaximal → ∃ i, ∀ z ∈ M, ∃ b c : B, b ∉ m ∧ (b : L) * z = c * a i)
    {z : L} (hz : z ∈ M) : z ∈ Submodule.span (𝓞 L) (Set.range a) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«InvertibleIdealIndexAlt».«mem_span_of_local» := P2M_GroundTheory_Heights__Heights_InvertibleIdealIndexAlt_mem_span_of_local_c35ca71026c1
