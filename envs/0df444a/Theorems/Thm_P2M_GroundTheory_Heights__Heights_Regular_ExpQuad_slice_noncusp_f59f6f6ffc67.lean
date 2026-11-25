-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_ExpQuad_slice_noncusp_f59f6f6ffc67
-- name    : P2M_GroundTheory_Heights__Heights_Regular_ExpQuad_slice_noncusp_f59f6f6ffc67
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T04:17:25.002986+00:00
-- url     : https://prove2.me/theorems/ff68176a-16fe-4f18-a6a2-4b047d4ac3fc
-- title:
--   P2 M Ground Theory Heights  Heights Regular Exp Quad slice noncusp f59f6f6ffc67: P2 M Ground Theory Heights  Heights Regular Exp Quad slice noncusp f59f6f6ffc67
-- statement:
--   The P2 M Ground Theory Heights  Heights Regular Exp Quad slice noncusp f59f6f6ffc67 construction uses the P2 M Ground Theory Heights  Heights Regular Exp Quad slice noncusp f59f6f6ffc67 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PExpExtension.lean#L264-L287
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PExpExtension.lean#L264-L287

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

theorem P2M_GroundTheory_Heights__Heights_Regular_ExpQuad_slice_noncusp_f59f6f6ffc67 {F : (Fin n → ℂ) → ℂ} (hF : AnalyticOnNhd ℂ F (puncturedChart P.a_le (ball 0 1)))
    {z : Fin n → ℂ} (hz : z ∈ ball (0 : Fin n → ℂ) 1) (m : Fin n) (hm : ¬ m.val < a)
    (hne : ∀ j, j ≠ m → z j ≠ 0) :
    ∃ c : ℂ, Tendsto (fun x => F (Function.update z m x)) (𝓝[≠] 0) (𝓝 c) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Regular».«ExpQuad».«slice_noncusp» := P2M_GroundTheory_Heights__Heights_Regular_ExpQuad_slice_noncusp_f59f6f6ffc67
