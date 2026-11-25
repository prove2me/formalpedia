-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FrameJacobianSumAlt_real_inner_eq_re_69fd56d86293
-- name    : P2M_GroundTheory_Heights__Heights_FrameJacobianSumAlt_real_inner_eq_re_69fd56d86293
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:18:24.815736+00:00
-- url     : https://prove2.me/theorems/c2932656-117e-49cb-b96b-086f868c2575
-- title:
--   P2 M Ground Theory Heights  Heights Frame Jacobian Sum Alt real inner eq re 69fd56d86293: P2 M Ground Theory Heights  Heights Frame Jacobian Sum Alt real inner eq re 69fd56d86293
-- statement:
--   The P2 M Ground Theory Heights  Heights Frame Jacobian Sum Alt real inner eq re 69fd56d86293 construction uses the P2 M Ground Theory Heights  Heights Frame Jacobian Sum Alt real inner eq re 69fd56d86293 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PFrameJacobianSum.lean#L16-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PFrameJacobianSum.lean#L16-L17

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFrameJacobianSum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PCauchyBinet
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFrameJacobianSum
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
open Matrix Finset Module
noncomputable section
open GroundTheory.Heights₂.Heights.FrameJacobianSumAlt
variable {d : ℕ} {ι : Type*} [Fintype ι]

theorem P2M_GroundTheory_Heights__Heights_FrameJacobianSumAlt_real_inner_eq_re_69fd56d86293 (x y : EuclideanSpace ℂ ι) : inner ℝ x y = (inner ℂ x y).re := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FrameJacobianSumAlt».«real_inner_eq_re» := P2M_GroundTheory_Heights__Heights_FrameJacobianSumAlt_real_inner_eq_re_69fd56d86293
