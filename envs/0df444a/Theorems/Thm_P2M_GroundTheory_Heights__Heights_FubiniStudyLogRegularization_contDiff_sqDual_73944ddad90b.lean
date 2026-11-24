-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FubiniStudyLogRegularization_contDiff_sqDual_73944ddad90b
-- name    : P2M_GroundTheory_Heights__Heights_FubiniStudyLogRegularization_contDiff_sqDual_73944ddad90b
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:02:42.321361+00:00
-- url     : https://prove2.me/theorems/fac1ca75-4d1e-4f93-9d34-687ebc4701e3
-- title:
--   P2 M Ground Theory Heights  Heights Fubini Study Log Regularization cont Diff sq Dual 73944ddad90b: P2 M Ground Theory Heights  Heights Fubini Study Log Regularization cont Diff sq Dual 73944ddad90b
-- statement:
--   The P2 M Ground Theory Heights  Heights Fubini Study Log Regularization cont Diff sq Dual 73944ddad90b construction uses the P2 M Ground Theory Heights  Heights Fubini Study Log Regularization cont Diff sq Dual 73944ddad90b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/FsLogRegBasic.lean#L37-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/FsLogRegBasic.lean#L37-L41

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

theorem P2M_GroundTheory_Heights__Heights_FubiniStudyLogRegularization_contDiff_sqDual_73944ddad90b (h : HermNorm n) : ContDiff ℝ ∞ (sqDual h) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FubiniStudyLogRegularization».«contDiff_sqDual» := P2M_GroundTheory_Heights__Heights_FubiniStudyLogRegularization_contDiff_sqDual_73944ddad90b
