-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PGaussShellSum_exp_neg_nat_4b21dec2f2be
-- name    : P2M_GroundTheory_Heights__Heights_PGaussShellSum_exp_neg_nat_4b21dec2f2be
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T04:14:05.52208+00:00
-- url     : https://prove2.me/theorems/35000633-862d-4ac7-abce-b3b29553e7d0
-- title:
--   P2 M Ground Theory Heights  Heights PGauss Shell Sum exp neg nat 4b21dec2f2be: P2 M Ground Theory Heights  Heights PGauss Shell Sum exp neg nat 4b21dec2f2be
-- statement:
--   The P2 M Ground Theory Heights  Heights PGauss Shell Sum exp neg nat 4b21dec2f2be construction uses the P2 M Ground Theory Heights  Heights PGauss Shell Sum exp neg nat 4b21dec2f2be property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PGaussShellSum.lean#L25-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PGaussShellSum.lean#L25-L28

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGauss
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PGaussShellSum
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
open GroundTheory.Heights₂.Heights.PGaussShellSum

theorem P2M_GroundTheory_Heights__Heights_PGaussShellSum_exp_neg_nat_4b21dec2f2be (m : ℕ) : Real.exp (-(m : ℝ)) = Real.exp (-1) ^ m := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PGaussShellSum».«exp_neg_nat» := P2M_GroundTheory_Heights__Heights_PGaussShellSum_exp_neg_nat_4b21dec2f2be
