-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_ExpQuad_qf_add_1afce1407430
-- name    : P2M_GroundTheory_Heights__Heights_Regular_ExpQuad_qf_add_1afce1407430
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:58:03.242+00:00
-- url     : https://prove2.me/theorems/a5f5f2c5-28e4-4b9d-802a-7226648eda56
-- title:
--   P2 M Ground Theory Heights  Heights Regular Exp Quad qf add 1afce1407430: P2 M Ground Theory Heights  Heights Regular Exp Quad qf add 1afce1407430
-- statement:
--   The P2 M Ground Theory Heights  Heights Regular Exp Quad qf add 1afce1407430 construction uses the P2 M Ground Theory Heights  Heights Regular Exp Quad qf add 1afce1407430 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PExpExtension.lean#L48-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PExpExtension.lean#L48-L50

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

theorem P2M_GroundTheory_Heights__Heights_Regular_ExpQuad_qf_add_1afce1407430 {g : ℕ} (A B : Matrix (Fin g) (Fin g) ℂ) (v : Fin g → ℤ) :
    qf (A + B) v = qf A v + qf B v := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Regular».«ExpQuad».«qf_add» := P2M_GroundTheory_Heights__Heights_Regular_ExpQuad_qf_add_1afce1407430
