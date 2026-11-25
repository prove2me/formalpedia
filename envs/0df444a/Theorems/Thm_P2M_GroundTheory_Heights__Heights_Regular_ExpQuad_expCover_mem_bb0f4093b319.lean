-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_ExpQuad_expCover_mem_bb0f4093b319
-- name    : P2M_GroundTheory_Heights__Heights_Regular_ExpQuad_expCover_mem_bb0f4093b319
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T04:18:25.565868+00:00
-- url     : https://prove2.me/theorems/08ee8f96-12c1-4fc1-a763-fa86a2323bb2
-- title:
--   P2 M Ground Theory Heights  Heights Regular Exp Quad exp Cover mem bb0f4093b319: P2 M Ground Theory Heights  Heights Regular Exp Quad exp Cover mem bb0f4093b319
-- statement:
--   The P2 M Ground Theory Heights  Heights Regular Exp Quad exp Cover mem bb0f4093b319 construction uses the P2 M Ground Theory Heights  Heights Regular Exp Quad exp Cover mem bb0f4093b319 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PExpExtension.lean#L183-L196
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PExpExtension.lean#L183-L196

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_StRiemannSlices
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_StPuncturedExpOrder
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_StLogCoverDescent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PExpExtension
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Regular
open Metric Filter Topology Matrix
noncomputable section
open GroundTheory.Heights₂.Heights.Regular.ExpQuad
variable {n a g : ℕ} (P : PeriodPolydisc n a g) (v : Fin g → ℤ)

theorem P2M_GroundTheory_Heights__Heights_Regular_ExpQuad_expCover_mem_bb0f4093b319 {w : Fin n → ℂ} (hw : w ∈ logCover P.a_le) :
    expCover a w ∈ puncturedChart P.a_le (ball 0 1) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Regular».«ExpQuad».«expCover_mem» := P2M_GroundTheory_Heights__Heights_Regular_ExpQuad_expCover_mem_bb0f4093b319
