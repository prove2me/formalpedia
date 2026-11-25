-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_KeyFormula_lineCoeff_shift_057157dc3f1b
-- name    : P2M_GroundTheory_Heights__Heights_KeyFormula_lineCoeff_shift_057157dc3f1b
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:25:51.867487+00:00
-- url     : https://prove2.me/theorems/1e1792dd-f3ed-5bbe-93b3-f69fc036c1ce
-- title:
--   P2 M Ground Theory Heights  Heights Key Formula line Coeff shift 057157dc3f1b: P2 M Ground Theory Heights  Heights Key Formula line Coeff shift 057157dc3f1b
-- statement:
--   The P2 M Ground Theory Heights  Heights Key Formula line Coeff shift 057157dc3f1b construction uses the P2 M Ground Theory Heights  Heights Key Formula line Coeff shift 057157dc3f1b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ThetaKeyFormula/ThetaThreeFamLinearIndependent.lean#L32-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ThetaKeyFormula/ThetaThreeFamLinearIndependent.lean#L32-L47

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

theorem P2M_GroundTheory_Heights__Heights_KeyFormula_lineCoeff_shift_057157dc3f1b (h : ℂ → ℂ) (n : ℕ) (C : ℂ)
    (h2 : ∀ w, h (w + I) = C * cexp (-2 * π * I * n * w) * h w) (k : ℤ) (y : ℝ) :
    lineCoeff h k (y + 1) = C * cexp (2 * π * k) * lineCoeff h (k + n) y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«KeyFormula».«lineCoeff_shift» := P2M_GroundTheory_Heights__Heights_KeyFormula_lineCoeff_shift_057157dc3f1b
