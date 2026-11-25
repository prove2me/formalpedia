-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PGaussConstant_exp_part_e2cb8cc4f20f
-- name    : P2M_GroundTheory_Heights__Heights_PGaussConstant_exp_part_e2cb8cc4f20f
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T04:13:17.151871+00:00
-- url     : https://prove2.me/theorems/7f994370-f795-55df-acba-0315582ae549
-- title:
--   P2 M Ground Theory Heights  Heights PGauss Constant exp part e2cb8cc4f20f: P2 M Ground Theory Heights  Heights PGauss Constant exp part e2cb8cc4f20f
-- statement:
--   The P2 M Ground Theory Heights  Heights PGauss Constant exp part e2cb8cc4f20f construction uses the P2 M Ground Theory Heights  Heights PGauss Constant exp part e2cb8cc4f20f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PGaussConstant.lean#L30-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PGaussConstant.lean#L30-L45

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGauss
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PGaussConstant
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
noncomputable section
open GroundTheory.Heights₂.Heights.PGaussConstant

theorem P2M_GroundTheory_Heights__Heights_PGaussConstant_exp_part_e2cb8cc4f20f (n : ℕ) (hn : 1 ≤ n) :
    2 * (Real.exp √(n : ℝ) * Real.exp ((n : ℝ) / (2 * π))) ≤ 2 ^ n * Real.exp 2 ^ n := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PGaussConstant».«exp_part» := P2M_GroundTheory_Heights__Heights_PGaussConstant_exp_part_e2cb8cc4f20f
