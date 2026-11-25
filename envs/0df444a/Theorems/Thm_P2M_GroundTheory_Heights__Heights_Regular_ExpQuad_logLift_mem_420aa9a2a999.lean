-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_ExpQuad_logLift_mem_420aa9a2a999
-- name    : P2M_GroundTheory_Heights__Heights_Regular_ExpQuad_logLift_mem_420aa9a2a999
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T04:17:11.5438+00:00
-- url     : https://prove2.me/theorems/ef27ea02-de1b-4d9f-bf01-14d44a38d5d2
-- title:
--   P2 M Ground Theory Heights  Heights Regular Exp Quad log Lift mem 420aa9a2a999: P2 M Ground Theory Heights  Heights Regular Exp Quad log Lift mem 420aa9a2a999
-- statement:
--   The P2 M Ground Theory Heights  Heights Regular Exp Quad log Lift mem 420aa9a2a999 construction uses the P2 M Ground Theory Heights  Heights Regular Exp Quad log Lift mem 420aa9a2a999 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PExpExtension.lean#L173-L181
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PExpExtension.lean#L173-L181

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

theorem P2M_GroundTheory_Heights__Heights_Regular_ExpQuad_logLift_mem_420aa9a2a999 {z : Fin n → ℂ} (hz : z ∈ puncturedChart P.a_le (ball 0 1)) :
    logLift a z ∈ logCover P.a_le := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Regular».«ExpQuad».«logLift_mem» := P2M_GroundTheory_Heights__Heights_Regular_ExpQuad_logLift_mem_420aa9a2a999
