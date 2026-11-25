-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_PtsRegLimit_abs_half_log_le_9e14d95ff747
-- name    : P2M_GroundTheory_Heights__Heights_Inter_PtsRegLimit_abs_half_log_le_9e14d95ff747
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T07:56:33.173825+00:00
-- url     : https://prove2.me/theorems/587645fa-4915-4c7a-9f6b-48acc0109824
-- title:
--   P2 M Ground Theory Heights  Heights Inter Pts Reg Limit abs half log le 9e14d95ff747: P2 M Ground Theory Heights  Heights Inter Pts Reg Limit abs half log le 9e14d95ff747
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Pts Reg Limit abs half log le 9e14d95ff747 construction uses the P2 M Ground Theory Heights  Heights Inter Pts Reg Limit abs half log le 9e14d95ff747 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PPtsRegLimit.lean#L14-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PPtsRegLimit.lean#L14-L26

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StPtsRegLimit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StPtsAbsIntegrable
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterFib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PPtsRegLimit
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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.ChartRestriction.G.Geo

theorem P2M_GroundTheory_Heights__Heights_Inter_PtsRegLimit_abs_half_log_le_9e14d95ff747 {x ε : ℝ} (hx : x ≠ 0) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    |Real.log (x ^ 2 + ε) / 2| ≤ |Real.log x| + |Real.log (x ^ 2 + 1) / 2| := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«PtsRegLimit».«abs_half_log_le» := P2M_GroundTheory_Heights__Heights_Inter_PtsRegLimit_abs_half_log_le_9e14d95ff747
