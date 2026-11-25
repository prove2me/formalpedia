-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_ExpQuad_analyticAt_coord_div_mul_a8bafecb8e64
-- name    : P2M_GroundTheory_Heights__Heights_Regular_ExpQuad_analyticAt_coord_div_mul_a8bafecb8e64
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T04:17:04.665865+00:00
-- url     : https://prove2.me/theorems/0fdd9926-1faf-4f59-90cc-e575cdde57c1
-- title:
--   P2 M Ground Theory Heights  Heights Regular Exp Quad analytic At coord div mul a8bafecb8e64: P2 M Ground Theory Heights  Heights Regular Exp Quad analytic At coord div mul a8bafecb8e64
-- statement:
--   The P2 M Ground Theory Heights  Heights Regular Exp Quad analytic At coord div mul a8bafecb8e64 construction uses the P2 M Ground Theory Heights  Heights Regular Exp Quad analytic At coord div mul a8bafecb8e64 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PExpExtension.lean#L75-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PExpExtension.lean#L75-L78

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

theorem P2M_GroundTheory_Heights__Heights_Regular_ExpQuad_analyticAt_coord_div_mul_a8bafecb8e64 {n : ℕ} (k : Fin n) (c d : ℂ) (w : Fin n → ℂ) :
    AnalyticAt ℂ (fun x : Fin n → ℂ => x k / c * d) w := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Regular».«ExpQuad».«analyticAt_coord_div_mul» := P2M_GroundTheory_Heights__Heights_Regular_ExpQuad_analyticAt_coord_div_mul_a8bafecb8e64
