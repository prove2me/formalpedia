-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_ExpQuad_slice_order_00de2034edca
-- name    : P2M_GroundTheory_Heights__Heights_Regular_ExpQuad_slice_order_00de2034edca
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T04:17:23.147022+00:00
-- url     : https://prove2.me/theorems/8e57504c-f397-4646-9dcf-3526838414a4
-- title:
--   P2 M Ground Theory Heights  Heights Regular Exp Quad slice order 00de2034edca: P2 M Ground Theory Heights  Heights Regular Exp Quad slice order 00de2034edca
-- statement:
--   The P2 M Ground Theory Heights  Heights Regular Exp Quad slice order 00de2034edca construction uses the P2 M Ground Theory Heights  Heights Regular Exp Quad slice order 00de2034edca property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PExpExtension.lean#L220-L262
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PExpExtension.lean#L220-L262

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

theorem P2M_GroundTheory_Heights__Heights_Regular_ExpQuad_slice_order_00de2034edca (hD : LogCoverDescent.Statement) (hO : PuncturedExpOrder.Statement)
    {z : Fin n → ℂ} (hz : z ∈ ball (0 : Fin n → ℂ) 1) (i : Fin a)
    (hne : ∀ j : Fin a, j ≠ i → z (Fin.castLE P.a_le j) ≠ 0) :
    0 ≤ intQuad (P.B i) v ∧ ∃ c : ℂ, c ≠ 0 ∧
      Tendsto (fun x => Complex.exp (psi P v (Function.update z (Fin.castLE P.a_le i) x)))
        (𝓝[≠] 0) (𝓝 c) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Regular».«ExpQuad».«slice_order» := P2M_GroundTheory_Heights__Heights_Regular_ExpQuad_slice_order_00de2034edca
