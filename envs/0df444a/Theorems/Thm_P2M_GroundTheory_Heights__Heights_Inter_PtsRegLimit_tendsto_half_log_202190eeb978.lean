-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_PtsRegLimit_tendsto_half_log_202190eeb978
-- name    : P2M_GroundTheory_Heights__Heights_Inter_PtsRegLimit_tendsto_half_log_202190eeb978
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T07:55:52.073597+00:00
-- url     : https://prove2.me/theorems/673c9ce1-2ad6-4dd8-905a-43b6f449b212
-- title:
--   P2 M Ground Theory Heights  Heights Inter Pts Reg Limit tendsto half log 202190eeb978: P2 M Ground Theory Heights  Heights Inter Pts Reg Limit tendsto half log 202190eeb978
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Pts Reg Limit tendsto half log 202190eeb978 construction uses the P2 M Ground Theory Heights  Heights Inter Pts Reg Limit tendsto half log 202190eeb978 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PPtsRegLimit.lean#L28-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PPtsRegLimit.lean#L28-L36

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

theorem P2M_GroundTheory_Heights__Heights_Inter_PtsRegLimit_tendsto_half_log_202190eeb978 {x : ℝ} (hx : x ≠ 0) :
    Tendsto (fun ε : ℝ => Real.log (x ^ 2 + ε) / 2) (𝓝[>] 0) (𝓝 (Real.log x)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«PtsRegLimit».«tendsto_half_log» := P2M_GroundTheory_Heights__Heights_Inter_PtsRegLimit_tendsto_half_log_202190eeb978
