-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PSymplMinExists_exists_lower_735580152940
-- name    : P2M_GroundTheory_Heights__Heights_PSymplMinExists_exists_lower_735580152940
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:14:21.240799+00:00
-- url     : https://prove2.me/theorems/47df3b5f-293b-4d20-87fa-0e8a4773802e
-- title:
--   P2 M Ground Theory Heights  Heights PSympl Min Exists exists lower 735580152940: P2 M Ground Theory Heights  Heights PSympl Min Exists exists lower 735580152940
-- statement:
--   The P2 M Ground Theory Heights  Heights PSympl Min Exists exists lower 735580152940 construction uses the P2 M Ground Theory Heights  Heights PSympl Min Exists exists lower 735580152940 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PSymplMinExists.lean#L20-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PSymplMinExists.lean#L20-L42

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsSympl
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PSymplMinExists
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open Matrix
open GroundTheory.Heights₂.Heights.PSymplMinExists
variable {ι : Type} [Fintype ι]

theorem P2M_GroundTheory_Heights__Heights_PSymplMinExists_exists_lower_735580152940 [DecidableEq ι] [Nonempty ι] (G : Matrix ι ι ℝ) (hG : G.PosDef) :
    ∃ μ : ℝ, 0 < μ ∧ ∀ x : ι → ℝ, μ * ‖x‖ ^ 2 ≤ qf G x := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PSymplMinExists».«exists_lower» := P2M_GroundTheory_Heights__Heights_PSymplMinExists_exists_lower_735580152940
