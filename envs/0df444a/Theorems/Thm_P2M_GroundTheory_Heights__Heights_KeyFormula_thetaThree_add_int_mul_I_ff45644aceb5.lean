-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_KeyFormula_thetaThree_add_int_mul_I_ff45644aceb5
-- name    : P2M_GroundTheory_Heights__Heights_KeyFormula_thetaThree_add_int_mul_I_ff45644aceb5
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:33:32.942861+00:00
-- url     : https://prove2.me/theorems/e0b6b9fb-b919-43b0-a1bb-4403999d30a9
-- title:
--   P2 M Ground Theory Heights  Heights Key Formula theta Three add int mul I ff45644aceb5: P2 M Ground Theory Heights  Heights Key Formula theta Three add int mul I ff45644aceb5
-- statement:
--   The P2 M Ground Theory Heights  Heights Key Formula theta Three add int mul I ff45644aceb5 construction uses the P2 M Ground Theory Heights  Heights Key Formula theta Three add int mul I ff45644aceb5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ThetaKeyFormula/ThetaThreeFamLinearIndependent.lean#L162-L168
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ThetaKeyFormula/ThetaThreeFamLinearIndependent.lean#L162-L168

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

theorem P2M_GroundTheory_Heights__Heights_KeyFormula_thetaThree_add_int_mul_I_ff45644aceb5 (ν : ℕ) (k : ℤ) (w : ℂ) :
    thetaThree ν (w + k * I) =
      cexp (-(3 * π * I * k ^ 2 * I) - 6 * π * I * k * w) * thetaThree ν w := by sorry

alias «GroundTheory».«Heights₂».«Heights».«KeyFormula».«thetaThree_add_int_mul_I» := P2M_GroundTheory_Heights__Heights_KeyFormula_thetaThree_add_int_mul_I_ff45644aceb5
