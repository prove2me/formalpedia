-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PGaussTermBound_pow_le_sqrt_pow_mul_exp_ac18c288441e
-- name    : P2M_GroundTheory_Heights__Heights_PGaussTermBound_pow_le_sqrt_pow_mul_exp_ac18c288441e
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T04:13:44.437283+00:00
-- url     : https://prove2.me/theorems/3ae6f78e-e90f-43c6-a09c-bc6726333de1
-- title:
--   P2 M Ground Theory Heights  Heights PGauss Term Bound pow le sqrt pow mul exp ac18c288441e: P2 M Ground Theory Heights  Heights PGauss Term Bound pow le sqrt pow mul exp ac18c288441e
-- statement:
--   The P2 M Ground Theory Heights  Heights PGauss Term Bound pow le sqrt pow mul exp ac18c288441e construction uses the P2 M Ground Theory Heights  Heights PGauss Term Bound pow le sqrt pow mul exp ac18c288441e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PGaussTermBound.lean#L11-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PGaussTermBound.lean#L11-L30

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

theorem P2M_GroundTheory_Heights__Heights_PGaussTermBound_pow_le_sqrt_pow_mul_exp_ac18c288441e (n m : ℕ) (hn : 1 ≤ n) :
    ((m : ℝ) + 1) ^ n ≤ √(n : ℝ) ^ n * Real.exp (√(n : ℝ) * ((m : ℝ) + 1)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PGaussTermBound».«pow_le_sqrt_pow_mul_exp» := P2M_GroundTheory_Heights__Heights_PGaussTermBound_pow_le_sqrt_pow_mul_exp_ac18c288441e
