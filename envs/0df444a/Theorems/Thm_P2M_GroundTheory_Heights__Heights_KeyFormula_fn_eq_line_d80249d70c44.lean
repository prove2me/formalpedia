-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_KeyFormula_fn_eq_line_d80249d70c44
-- name    : P2M_GroundTheory_Heights__Heights_KeyFormula_fn_eq_line_d80249d70c44
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:26:59.990255+00:00
-- url     : https://prove2.me/theorems/e2d7c8db-5d73-4653-bb92-b94c26b2381b
-- title:
--   P2 M Ground Theory Heights  Heights Key Formula fn eq line d80249d70c44: P2 M Ground Theory Heights  Heights Key Formula fn eq line d80249d70c44
-- statement:
--   The P2 M Ground Theory Heights  Heights Key Formula fn eq line d80249d70c44 construction uses the P2 M Ground Theory Heights  Heights Key Formula fn eq line d80249d70c44 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ThetaKeyFormula/ThetaThreeFamLinearIndependent.lean#L251-L252
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ThetaKeyFormula/ThetaThreeFamLinearIndependent.lean#L251-L252

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

theorem P2M_GroundTheory_Heights__Heights_KeyFormula_fn_eq_line_d80249d70c44 (f : (Fin 1 → ℂ) → ℂ) (z : Fin 1 → ℂ) : f z = f (fun _ => z 0) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«KeyFormula».«fn_eq_line» := P2M_GroundTheory_Heights__Heights_KeyFormula_fn_eq_line_d80249d70c44
