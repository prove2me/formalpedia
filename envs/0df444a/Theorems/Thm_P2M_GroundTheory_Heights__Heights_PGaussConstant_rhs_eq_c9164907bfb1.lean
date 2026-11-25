-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PGaussConstant_rhs_eq_c9164907bfb1
-- name    : P2M_GroundTheory_Heights__Heights_PGaussConstant_rhs_eq_c9164907bfb1
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T04:13:48.2924+00:00
-- url     : https://prove2.me/theorems/5ef49742-6c18-4066-836b-7c58f78cac20
-- title:
--   P2 M Ground Theory Heights  Heights PGauss Constant rhs eq c9164907bfb1: P2 M Ground Theory Heights  Heights PGauss Constant rhs eq c9164907bfb1
-- statement:
--   The P2 M Ground Theory Heights  Heights PGauss Constant rhs eq c9164907bfb1 construction uses the P2 M Ground Theory Heights  Heights PGauss Constant rhs eq c9164907bfb1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PGaussConstant.lean#L13-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PGaussConstant.lean#L13-L28

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

theorem P2M_GroundTheory_Heights__Heights_PGaussConstant_rhs_eq_c9164907bfb1 (n : ℕ) :
    (72 * Real.exp 4 * (n : ℝ)) ^ ((n : ℝ) / 2) = (6 * √2 * Real.exp 2 * √(n : ℝ)) ^ n := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PGaussConstant».«rhs_eq» := P2M_GroundTheory_Heights__Heights_PGaussConstant_rhs_eq_c9164907bfb1
