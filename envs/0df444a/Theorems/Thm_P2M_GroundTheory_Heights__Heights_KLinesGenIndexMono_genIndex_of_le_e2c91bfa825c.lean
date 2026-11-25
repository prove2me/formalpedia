-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_KLinesGenIndexMono_genIndex_of_le_e2c91bfa825c
-- name    : P2M_GroundTheory_Heights__Heights_KLinesGenIndexMono_genIndex_of_le_e2c91bfa825c
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:27:11.100951+00:00
-- url     : https://prove2.me/theorems/575a878a-2dbb-4e09-8fb7-5b8042923b3d
-- title:
--   P2 M Ground Theory Heights  Heights KLines Gen Index Mono gen Index of le e2c91bfa825c: P2 M Ground Theory Heights  Heights KLines Gen Index Mono gen Index of le e2c91bfa825c
-- statement:
--   The P2 M Ground Theory Heights  Heights KLines Gen Index Mono gen Index of le e2c91bfa825c construction uses the P2 M Ground Theory Heights  Heights KLines Gen Index Mono gen Index of le e2c91bfa825c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PLinesGenIndexMono.lean#L9-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PLinesGenIndexMono.lean#L9-L12

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLines
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PLinesGenIndexMono
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
open GroundTheory.Heights₂.Heights.KLinesGenIndexMono

theorem P2M_GroundTheory_Heights__Heights_KLinesGenIndexMono_genIndex_of_le_e2c91bfa825c {G : Type*} [AddCommGroup G] {A A' : AddSubgroup G} (h : A ≤ A') :
    genIndex A' A = (A.relIndex A' : ℝ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«KLinesGenIndexMono».«genIndex_of_le» := P2M_GroundTheory_Heights__Heights_KLinesGenIndexMono_genIndex_of_le_e2c91bfa825c
