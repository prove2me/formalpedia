-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_KeyFormula_thetaThree_zero_finite_acc1125a749b
-- name    : P2M_GroundTheory_Heights__Heights_KeyFormula_thetaThree_zero_finite_acc1125a749b
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:26:44.767022+00:00
-- url     : https://prove2.me/theorems/4e9efbb5-3f7d-4c5c-acb5-e48779e10b3a
-- title:
--   P2 M Ground Theory Heights  Heights Key Formula theta Three zero finite acc1125a749b: P2 M Ground Theory Heights  Heights Key Formula theta Three zero finite acc1125a749b
-- statement:
--   The P2 M Ground Theory Heights  Heights Key Formula theta Three zero finite acc1125a749b construction uses the P2 M Ground Theory Heights  Heights Key Formula theta Three zero finite acc1125a749b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ThetaKeyFormula/ThetaThreeFamLinearIndependent.lean#L359-L396
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ThetaKeyFormula/ThetaThreeFamLinearIndependent.lean#L359-L396

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

theorem P2M_GroundTheory_Heights__Heights_KeyFormula_thetaThree_zero_finite_acc1125a749b :
    ∃ W : Finset ℂ, ∀ w, thetaThree 0 w = 0 → ∃ w' ∈ W, ∃ m k : ℤ, w = w' + k * I + m := by sorry

alias «GroundTheory».«Heights₂».«Heights».«KeyFormula».«thetaThree_zero_finite» := P2M_GroundTheory_Heights__Heights_KeyFormula_thetaThree_zero_finite_acc1125a749b
