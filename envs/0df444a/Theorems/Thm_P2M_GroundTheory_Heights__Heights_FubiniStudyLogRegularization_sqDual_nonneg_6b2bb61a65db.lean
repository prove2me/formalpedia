-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FubiniStudyLogRegularization_sqDual_nonneg_6b2bb61a65db
-- name    : P2M_GroundTheory_Heights__Heights_FubiniStudyLogRegularization_sqDual_nonneg_6b2bb61a65db
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:03:08.325337+00:00
-- url     : https://prove2.me/theorems/4fb0fdca-ef65-492c-bef4-ad2306ac4c9e
-- title:
--   P2 M Ground Theory Heights  Heights Fubini Study Log Regularization sq Dual nonneg 6b2bb61a65db: P2 M Ground Theory Heights  Heights Fubini Study Log Regularization sq Dual nonneg 6b2bb61a65db
-- statement:
--   The P2 M Ground Theory Heights  Heights Fubini Study Log Regularization sq Dual nonneg 6b2bb61a65db construction uses the P2 M Ground Theory Heights  Heights Fubini Study Log Regularization sq Dual nonneg 6b2bb61a65db property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/FsLogRegBasic.lean#L23-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/FsLogRegBasic.lean#L23-L24

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

theorem P2M_GroundTheory_Heights__Heights_FubiniStudyLogRegularization_sqDual_nonneg_6b2bb61a65db (h : HermNorm n) (y : Fin n → ℂ) : 0 ≤ sqDual h y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FubiniStudyLogRegularization».«sqDual_nonneg» := P2M_GroundTheory_Heights__Heights_FubiniStudyLogRegularization_sqDual_nonneg_6b2bb61a65db
