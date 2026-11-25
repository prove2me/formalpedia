-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_KLinesFischer_toBlocks___eq_b092c100365c
-- name    : P2M_GroundTheory_Heights__Heights_KLinesFischer_toBlocks___eq_b092c100365c
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:26:45.42501+00:00
-- url     : https://prove2.me/theorems/ba64fe99-681c-4186-866f-b55a2924b115
-- title:
--   P2 M Ground Theory Heights  Heights KLines Fischer to Blocks   eq b092c100365c: P2 M Ground Theory Heights  Heights KLines Fischer to Blocks   eq b092c100365c
-- statement:
--   The P2 M Ground Theory Heights  Heights KLines Fischer to Blocks   eq b092c100365c construction uses the P2 M Ground Theory Heights  Heights KLines Fischer to Blocks   eq b092c100365c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PLinesFischer.lean#L13-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PLinesFischer.lean#L13-L17

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLines
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_DetIneq
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PLinesFischer
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
open scoped ComplexOrder
open GroundTheory.Heights₂.Heights.KLinesFischer

theorem P2M_GroundTheory_Heights__Heights_KLinesFischer_toBlocks___eq_b092c100365c {m k : Type*} {M : Matrix (m ⊕ k) (m ⊕ k) ℂ} (hM : M.IsHermitian) :
    M.toBlocks₂₁ = M.toBlocks₁₂ᴴ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«KLinesFischer».«toBlocks₂₁_eq» := P2M_GroundTheory_Heights__Heights_KLinesFischer_toBlocks___eq_b092c100365c
