-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RegConeLimit_measurable_fsLogReg_pointOf_9f16abb635bc
-- name    : P2M_GroundTheory_Heights__Heights_RegConeLimit_measurable_fsLogReg_pointOf_9f16abb635bc
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T04:15:42.031808+00:00
-- url     : https://prove2.me/theorems/d4b6ca4f-e948-48a1-9590-ec3b071255cd
-- title:
--   P2 M Ground Theory Heights  Heights Reg Cone Limit measurable fs Log Reg point Of 9f16abb635bc: P2 M Ground Theory Heights  Heights Reg Cone Limit measurable fs Log Reg point Of 9f16abb635bc
-- statement:
--   The P2 M Ground Theory Heights  Heights Reg Cone Limit measurable fs Log Reg point Of 9f16abb635bc construction uses the P2 M Ground Theory Heights  Heights Reg Cone Limit measurable fs Log Reg point Of 9f16abb635bc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PRegConeLimit.lean#L61-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PRegConeLimit.lean#L61-L74

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsGreenReg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ConeBall
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeFsLogIntegrable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PRegConeLimit
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
open MvPolynomial MeasureTheory Filter Topology Set ConeFsLog
noncomputable section
open GroundTheory.Heights₂.Heights.RegConeLimit
variable {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_RegConeLimit_measurable_fsLogReg_pointOf_9f16abb635bc (h : HermNorm n) (u : Fin n → ℂ) (ε : ℝ) :
    Measurable fun y : EuclideanSpace ℂ (Fin n) => fsLogReg h u ε (h.pointOf y) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RegConeLimit».«measurable_fsLogReg_pointOf» := P2M_GroundTheory_Heights__Heights_RegConeLimit_measurable_fsLogReg_pointOf_9f16abb635bc
