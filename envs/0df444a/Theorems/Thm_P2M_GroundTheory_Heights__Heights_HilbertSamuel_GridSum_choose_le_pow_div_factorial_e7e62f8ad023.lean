-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_GridSum_choose_le_pow_div_factorial_e7e62f8ad023
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_GridSum_choose_le_pow_div_factorial_e7e62f8ad023
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T03:18:57.296006+00:00
-- url     : https://prove2.me/theorems/45482c50-ea92-4b81-94cb-584db89c48b7
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Grid Sum choose le pow div factorial e7e62f8ad023: P2 M Ground Theory Heights  Heights Hilbert Samuel Grid Sum choose le pow div factorial e7e62f8ad0
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Grid Sum choose le pow div factorial e7e62f8ad023 construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Grid Sum choose le pow div factorial e7e62f8ad023 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PGridSum.lean#L38-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PGridSum.lean#L38-L44

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

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_GridSum_choose_le_pow_div_factorial_e7e62f8ad023 (a i : ℕ) :
    (a.choose i : ℝ) ≤ (a : ℝ) ^ i / (i.factorial : ℝ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«GridSum».«choose_le_pow_div_factorial» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_GridSum_choose_le_pow_div_factorial_e7e62f8ad023
