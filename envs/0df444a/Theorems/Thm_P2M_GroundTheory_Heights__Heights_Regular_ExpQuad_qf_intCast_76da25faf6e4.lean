-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_ExpQuad_qf_intCast_76da25faf6e4
-- name    : P2M_GroundTheory_Heights__Heights_Regular_ExpQuad_qf_intCast_76da25faf6e4
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T04:17:45.770204+00:00
-- url     : https://prove2.me/theorems/a666a9ad-06e9-40af-a1b6-e7c2bd5980d9
-- title:
--   P2 M Ground Theory Heights  Heights Regular Exp Quad qf int Cast 76da25faf6e4: P2 M Ground Theory Heights  Heights Regular Exp Quad qf int Cast 76da25faf6e4
-- statement:
--   The P2 M Ground Theory Heights  Heights Regular Exp Quad qf int Cast 76da25faf6e4 construction uses the P2 M Ground Theory Heights  Heights Regular Exp Quad qf int Cast 76da25faf6e4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PExpExtension.lean#L63-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PExpExtension.lean#L63-L65

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

theorem P2M_GroundTheory_Heights__Heights_Regular_ExpQuad_qf_intCast_76da25faf6e4 {g : ℕ} (B : Matrix (Fin g) (Fin g) ℤ) (v : Fin g → ℤ) :
    qf (B.map (Int.cast : ℤ → ℂ)) v = ((intQuad B v : ℤ) : ℂ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Regular».«ExpQuad».«qf_intCast» := P2M_GroundTheory_Heights__Heights_Regular_ExpQuad_qf_intCast_76da25faf6e4
