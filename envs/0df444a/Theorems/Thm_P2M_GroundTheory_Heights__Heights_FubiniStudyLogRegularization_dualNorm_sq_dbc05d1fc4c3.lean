-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FubiniStudyLogRegularization_dualNorm_sq_dbc05d1fc4c3
-- name    : P2M_GroundTheory_Heights__Heights_FubiniStudyLogRegularization_dualNorm_sq_dbc05d1fc4c3
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:03:05.030432+00:00
-- url     : https://prove2.me/theorems/8af631ea-6d13-4de3-907c-f016cc068cd3
-- title:
--   P2 M Ground Theory Heights  Heights Fubini Study Log Regularization dual Norm sq dbc05d1fc4c3: P2 M Ground Theory Heights  Heights Fubini Study Log Regularization dual Norm sq dbc05d1fc4c3
-- statement:
--   The P2 M Ground Theory Heights  Heights Fubini Study Log Regularization dual Norm sq dbc05d1fc4c3 construction uses the P2 M Ground Theory Heights  Heights Fubini Study Log Regularization dual Norm sq dbc05d1fc4c3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/FsLogRegBasic.lean#L26-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/FsLogRegBasic.lean#L26-L27

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

theorem P2M_GroundTheory_Heights__Heights_FubiniStudyLogRegularization_dualNorm_sq_dbc05d1fc4c3 (h : HermNorm n) (y : Fin n → ℂ) : h.dualNorm y ^ 2 = sqDual h y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FubiniStudyLogRegularization».«dualNorm_sq» := P2M_GroundTheory_Heights__Heights_FubiniStudyLogRegularization_dualNorm_sq_dbc05d1fc4c3
