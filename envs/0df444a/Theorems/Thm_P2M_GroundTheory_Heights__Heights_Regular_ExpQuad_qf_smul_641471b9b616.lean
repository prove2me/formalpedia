-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_ExpQuad_qf_smul_641471b9b616
-- name    : P2M_GroundTheory_Heights__Heights_Regular_ExpQuad_qf_smul_641471b9b616
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T04:17:39.15918+00:00
-- url     : https://prove2.me/theorems/6bab75a2-746d-455e-982c-46f072e111ed
-- title:
--   P2 M Ground Theory Heights  Heights Regular Exp Quad qf smul 641471b9b616: P2 M Ground Theory Heights  Heights Regular Exp Quad qf smul 641471b9b616
-- statement:
--   The P2 M Ground Theory Heights  Heights Regular Exp Quad qf smul 641471b9b616 construction uses the P2 M Ground Theory Heights  Heights Regular Exp Quad qf smul 641471b9b616 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PExpExtension.lean#L52-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PExpExtension.lean#L52-L54

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

theorem P2M_GroundTheory_Heights__Heights_Regular_ExpQuad_qf_smul_641471b9b616 {g : ℕ} (c : ℂ) (A : Matrix (Fin g) (Fin g) ℂ) (v : Fin g → ℤ) :
    qf (c • A) v = c * qf A v := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Regular».«ExpQuad».«qf_smul» := P2M_GroundTheory_Heights__Heights_Regular_ExpQuad_qf_smul_641471b9b616
