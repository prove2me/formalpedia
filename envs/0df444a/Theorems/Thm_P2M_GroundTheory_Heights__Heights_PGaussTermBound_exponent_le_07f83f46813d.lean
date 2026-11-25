-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PGaussTermBound_exponent_le_07f83f46813d
-- name    : P2M_GroundTheory_Heights__Heights_PGaussTermBound_exponent_le_07f83f46813d
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T04:13:51.459123+00:00
-- url     : https://prove2.me/theorems/7fd25421-8ae6-4674-ad0c-6df162a217a8
-- title:
--   P2 M Ground Theory Heights  Heights PGauss Term Bound exponent le 07f83f46813d: P2 M Ground Theory Heights  Heights PGauss Term Bound exponent le 07f83f46813d
-- statement:
--   The P2 M Ground Theory Heights  Heights PGauss Term Bound exponent le 07f83f46813d construction uses the P2 M Ground Theory Heights  Heights PGauss Term Bound exponent le 07f83f46813d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PGaussTermBound.lean#L32-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PGaussTermBound.lean#L32-L48

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGauss
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PGaussTermBound
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
open Real
open GroundTheory.Heights₂.Heights.PGaussTermBound

theorem P2M_GroundTheory_Heights__Heights_PGaussTermBound_exponent_le_07f83f46813d (n m : ℕ) :
    √(n : ℝ) * ((m : ℝ) + 1) + -π * (m : ℝ) ^ 2 ≤ √(n : ℝ) + n / (2 * π) + -(m : ℝ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PGaussTermBound».«exponent_le» := P2M_GroundTheory_Heights__Heights_PGaussTermBound_exponent_le_07f83f46813d
