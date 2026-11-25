-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_GridSum_pow_sub_pow_le_0e7651b435b6
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_GridSum_pow_sub_pow_le_0e7651b435b6
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T03:19:00.337323+00:00
-- url     : https://prove2.me/theorems/0beb4fb7-5f1b-47fa-8a7c-bab7a780a01a
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Grid Sum pow sub pow le 0e7651b435b6: P2 M Ground Theory Heights  Heights Hilbert Samuel Grid Sum pow sub pow le 0e7651b435b6
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Grid Sum pow sub pow le 0e7651b435b6 construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Grid Sum pow sub pow le 0e7651b435b6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PGridSum.lean#L55-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PGridSum.lean#L55-L71

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsLattice
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PGridSum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open Finset Filter Asymptotics

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_GridSum_pow_sub_pow_le_0e7651b435b6 (x y : ℝ) (k : ℕ) (hy : 0 ≤ y) (hxy : y ≤ x) :
    x ^ k - y ^ k ≤ k * (x - y) * x ^ (k - 1) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«GridSum».«pow_sub_pow_le» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_GridSum_pow_sub_pow_le_0e7651b435b6
