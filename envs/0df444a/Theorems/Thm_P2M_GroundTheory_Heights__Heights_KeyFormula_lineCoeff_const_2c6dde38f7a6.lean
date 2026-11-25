-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_KeyFormula_lineCoeff_const_2c6dde38f7a6
-- name    : P2M_GroundTheory_Heights__Heights_KeyFormula_lineCoeff_const_2c6dde38f7a6
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:25:45.361702+00:00
-- url     : https://prove2.me/theorems/5c11c727-b11e-559f-8d6a-3c3f4cc4ed33
-- title:
--   P2 M Ground Theory Heights  Heights Key Formula line Coeff const 2c6dde38f7a6: P2 M Ground Theory Heights  Heights Key Formula line Coeff const 2c6dde38f7a6
-- statement:
--   The P2 M Ground Theory Heights  Heights Key Formula line Coeff const 2c6dde38f7a6 construction uses the P2 M Ground Theory Heights  Heights Key Formula line Coeff const 2c6dde38f7a6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ThetaKeyFormula/ThetaThreeFamLinearIndependent.lean#L14-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ThetaKeyFormula/ThetaThreeFamLinearIndependent.lean#L14-L30

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ThetaKeyFormula_RigSymFormTauINontrivial
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ThetaKeyFormula_ThetaThreeFamLinearIndependent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.KeyFormula
open Complex Real MeasureTheory intervalIntegral Matrix
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_KeyFormula_lineCoeff_const_2c6dde38f7a6 (h : ℂ → ℂ) (hd : Differentiable ℂ h) (h1 : ∀ w, h (w + 1) = h w)
    (k : ℤ) (y₁ y₂ : ℝ) : lineCoeff h k y₁ = lineCoeff h k y₂ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«KeyFormula».«lineCoeff_const» := P2M_GroundTheory_Heights__Heights_KeyFormula_lineCoeff_const_2c6dde38f7a6
