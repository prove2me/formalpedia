-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_ExpQuad_qf_sum_4e58130a36e0
-- name    : P2M_GroundTheory_Heights__Heights_Regular_ExpQuad_qf_sum_4e58130a36e0
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T04:17:19.675638+00:00
-- url     : https://prove2.me/theorems/b5091d70-1f81-48cc-b829-f0be1b5b8bf5
-- title:
--   P2 M Ground Theory Heights  Heights Regular Exp Quad qf sum 4e58130a36e0: P2 M Ground Theory Heights  Heights Regular Exp Quad qf sum 4e58130a36e0
-- statement:
--   The P2 M Ground Theory Heights  Heights Regular Exp Quad qf sum 4e58130a36e0 construction uses the P2 M Ground Theory Heights  Heights Regular Exp Quad qf sum 4e58130a36e0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PExpExtension.lean#L56-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PExpExtension.lean#L56-L61

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

theorem P2M_GroundTheory_Heights__Heights_Regular_ExpQuad_qf_sum_4e58130a36e0 {g : ℕ} {ι : Type*} (s : Finset ι) (A : ι → Matrix (Fin g) (Fin g) ℂ) (v : Fin g → ℤ) :
    qf (∑ i ∈ s, A i) v = ∑ i ∈ s, qf (A i) v := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Regular».«ExpQuad».«qf_sum» := P2M_GroundTheory_Heights__Heights_Regular_ExpQuad_qf_sum_4e58130a36e0
