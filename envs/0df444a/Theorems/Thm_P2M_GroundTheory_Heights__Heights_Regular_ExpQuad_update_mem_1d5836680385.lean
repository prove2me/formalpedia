-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_ExpQuad_update_mem_1d5836680385
-- name    : P2M_GroundTheory_Heights__Heights_Regular_ExpQuad_update_mem_1d5836680385
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T04:17:39.38797+00:00
-- url     : https://prove2.me/theorems/63205abd-2fe9-4b7d-9949-0cd62c8129fd
-- title:
--   P2 M Ground Theory Heights  Heights Regular Exp Quad update mem 1d5836680385: P2 M Ground Theory Heights  Heights Regular Exp Quad update mem 1d5836680385
-- statement:
--   The P2 M Ground Theory Heights  Heights Regular Exp Quad update mem 1d5836680385 construction uses the P2 M Ground Theory Heights  Heights Regular Exp Quad update mem 1d5836680385 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PExpExtension.lean#L200-L218
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PExpExtension.lean#L200-L218

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

theorem P2M_GroundTheory_Heights__Heights_Regular_ExpQuad_update_mem_1d5836680385 {z : Fin n → ℂ} (hz : z ∈ ball (0 : Fin n → ℂ) 1) (i : Fin a)
    (hne : ∀ j : Fin a, j ≠ i → z (Fin.castLE P.a_le j) ≠ 0) {x : ℂ}
    (hx : x ∈ ball (0 : ℂ) 1 \ {0}) :
    Function.update z (Fin.castLE P.a_le i) x ∈ puncturedChart P.a_le (ball 0 1) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Regular».«ExpQuad».«update_mem» := P2M_GroundTheory_Heights__Heights_Regular_ExpQuad_update_mem_1d5836680385
