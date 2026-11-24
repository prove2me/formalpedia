-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_le_of_isArithVar_pblk_fb6970ea00bb
-- name    : P2M_GroundTheory_Heights__Heights_le_of_isArithVar_pblk_fb6970ea00bb
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:44:04.499813+00:00
-- url     : https://prove2.me/theorems/74bbd830-2585-4197-bdff-851cee2e2320
-- title:
--   P2 M Ground Theory Heights  Heights le of is Arith Var pblk fb6970ea00bb: P2 M Ground Theory Heights  Heights le of is Arith Var pblk fb6970ea00bb
-- statement:
--   The P2 M Ground Theory Heights  Heights le of is Arith Var pblk fb6970ea00bb construction uses the P2 M Ground Theory Heights  Heights le of is Arith Var pblk fb6970ea00bb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeChartArea.lean#L43-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeChartArea.lean#L43-L54

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeSheetArea
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeChartArea
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial MeasureTheory Matrix Metric Set
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsArithVar IsGoodProj IsSheet fibre mcPts)

theorem P2M_GroundTheory_Heights__Heights_le_of_isArithVar_pblk_fb6970ea00bb {n d : ℕ} {P : Ideal (MRing (PBlk n))} (hP : IsArithVar P d) :
    d ≤ n := by sorry

alias «GroundTheory».«Heights₂».«Heights».«le_of_isArithVar_pblk» := P2M_GroundTheory_Heights__Heights_le_of_isArithVar_pblk_fb6970ea00bb
