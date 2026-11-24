-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FubiniStudyLogRegularization_sqDual_pos_386ce14d2e20
-- name    : P2M_GroundTheory_Heights__Heights_FubiniStudyLogRegularization_sqDual_pos_386ce14d2e20
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T23:56:41.754337+00:00
-- url     : https://prove2.me/theorems/46e23816-83d9-420d-9dfa-a33097211308
-- title:
--   P2 M Ground Theory Heights  Heights Fubini Study Log Regularization sq Dual pos 386ce14d2e20: P2 M Ground Theory Heights  Heights Fubini Study Log Regularization sq Dual pos 386ce14d2e20
-- statement:
--   The P2 M Ground Theory Heights  Heights Fubini Study Log Regularization sq Dual pos 386ce14d2e20 construction uses the P2 M Ground Theory Heights  Heights Fubini Study Log Regularization sq Dual pos 386ce14d2e20 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/FsLogRegBasic.lean#L29-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/FsLogRegBasic.lean#L29-L31

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsGreenReg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeLogBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PFsLogSmul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_FsLogRegBasic
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
open Matrix MeasureTheory
open scoped ContDiff
noncomputable section
open GroundTheory.Heights₂.Heights.FubiniStudyLogRegularization
variable {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_FubiniStudyLogRegularization_sqDual_pos_386ce14d2e20 (h : HermNorm n) {y : Fin n → ℂ} (hy : y ≠ 0) : 0 < sqDual h y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FubiniStudyLogRegularization».«sqDual_pos» := P2M_GroundTheory_Heights__Heights_FubiniStudyLogRegularization_sqDual_pos_386ce14d2e20
