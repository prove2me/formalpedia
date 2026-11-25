-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RegConeLimit_abs_fsLogReg_pointOf_le_cc18305be98c
-- name    : P2M_GroundTheory_Heights__Heights_RegConeLimit_abs_fsLogReg_pointOf_le_cc18305be98c
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T04:15:59.561352+00:00
-- url     : https://prove2.me/theorems/e1c7cd50-974e-42e2-9d42-a8490da183d6
-- title:
--   P2 M Ground Theory Heights  Heights Reg Cone Limit abs fs Log Reg point Of le cc18305be98c: P2 M Ground Theory Heights  Heights Reg Cone Limit abs fs Log Reg point Of le cc18305be98c
-- statement:
--   The P2 M Ground Theory Heights  Heights Reg Cone Limit abs fs Log Reg point Of le cc18305be98c construction uses the P2 M Ground Theory Heights  Heights Reg Cone Limit abs fs Log Reg point Of le cc18305be98c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PRegConeLimit.lean#L17-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PRegConeLimit.lean#L17-L59

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

theorem P2M_GroundTheory_Heights__Heights_RegConeLimit_abs_fsLogReg_pointOf_le_cc18305be98c (h : HermNorm n) (u : Fin n → ℂ) (y : EuclideanSpace ℂ (Fin n))
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hs : ∑ j, u j * h.pointOf y j ≠ 0) :
    |fsLogReg h u ε (h.pointOf y)| ≤
      |fsLog h u (h.pointOf y)| + Real.log (h.norm u ^ 2 + 1) / 2 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RegConeLimit».«abs_fsLogReg_pointOf_le» := P2M_GroundTheory_Heights__Heights_RegConeLimit_abs_fsLogReg_pointOf_le_cc18305be98c
