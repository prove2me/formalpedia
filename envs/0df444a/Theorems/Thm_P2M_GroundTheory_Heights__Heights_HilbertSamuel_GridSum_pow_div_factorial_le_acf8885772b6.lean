-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_GridSum_pow_div_factorial_le_acf8885772b6
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_GridSum_pow_div_factorial_le_acf8885772b6
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T03:19:21.551584+00:00
-- url     : https://prove2.me/theorems/caaabe0a-793b-4b10-ae46-ef2fc8e6ef5b
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Grid Sum pow div factorial le acf8885772b6: P2 M Ground Theory Heights  Heights Hilbert Samuel Grid Sum pow div factorial le acf8885772b6
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Grid Sum pow div factorial le acf8885772b6 construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Grid Sum pow div factorial le acf8885772b6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PGridSum.lean#L46-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PGridSum.lean#L46-L53

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

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_GridSum_pow_div_factorial_le_acf8885772b6 (a i : ℕ) :
    (a : ℝ) ^ i / (i.factorial : ℝ) ≤ ((a + i).choose i : ℝ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«GridSum».«pow_div_factorial_le» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_GridSum_pow_div_factorial_le_acf8885772b6
