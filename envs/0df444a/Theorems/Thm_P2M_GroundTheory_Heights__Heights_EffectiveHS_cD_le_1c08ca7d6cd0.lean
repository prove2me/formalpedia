-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_EffectiveHS_cD_le_1c08ca7d6cd0
-- name    : P2M_GroundTheory_Heights__Heights_EffectiveHS_cD_le_1c08ca7d6cd0
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:16:10.367677+00:00
-- url     : https://prove2.me/theorems/383886cb-af2d-58fc-85e5-8083ebddb82a
-- title:
--   P2 M Ground Theory Heights  Heights Effective HS c D le 1c08ca7d6cd0: P2 M Ground Theory Heights  Heights Effective HS c D le 1c08ca7d6cd0
-- statement:
--   The P2 M Ground Theory Heights  Heights Effective HS c D le 1c08ca7d6cd0 construction uses the P2 M Ground Theory Heights  Heights Effective HS c D le 1c08ca7d6cd0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/EffectiveHilbertSamuel/PDivision.lean#L176-L182
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/EffectiveHilbertSamuel/PDivision.lean#L176-L182

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_EffectiveHilbertSamuel_PConstants
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_EffectiveHilbertSamuel_PDivision
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
open GroundTheory.Heights₂.Heights.EffectiveHS
open Finset
open MeasureTheory

theorem P2M_GroundTheory_Heights__Heights_EffectiveHS_cD_le_1c08ca7d6cd0 (D : ℕ) : cD D ≤ 2 * (2 * Real.pi) ^ D := by sorry

alias «GroundTheory».«Heights₂».«Heights».«EffectiveHS».«cD_le» := P2M_GroundTheory_Heights__Heights_EffectiveHS_cD_le_1c08ca7d6cd0
