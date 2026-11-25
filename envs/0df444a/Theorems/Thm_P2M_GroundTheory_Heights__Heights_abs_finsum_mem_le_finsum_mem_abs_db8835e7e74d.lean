-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_abs_finsum_mem_le_finsum_mem_abs_db8835e7e74d
-- name    : P2M_GroundTheory_Heights__Heights_abs_finsum_mem_le_finsum_mem_abs_db8835e7e74d
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T04:44:39.34631+00:00
-- url     : https://prove2.me/theorems/482b2ef9-9221-46b4-b3df-4760a5edbe7f
-- title:
--   P2 M Ground Theory Heights  Heights abs finsum mem le finsum mem abs db8835e7e74d: P2 M Ground Theory Heights  Heights abs finsum mem le finsum mem abs db8835e7e74d
-- statement:
--   The P2 M Ground Theory Heights  Heights abs finsum mem le finsum mem abs db8835e7e74d construction uses the P2 M Ground Theory Heights  Heights abs finsum mem le finsum mem abs db8835e7e74d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PtsIntegrable.lean#L13-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PtsIntegrable.lean#L13-L32

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StPtsAbsIntegrable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StPtsSumMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PtsIntegrable
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
open MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo

theorem P2M_GroundTheory_Heights__Heights_abs_finsum_mem_le_finsum_mem_abs_db8835e7e74d {α : Type*} (S : Set α) (f : α → ℝ) :
    |∑ᶠ w ∈ S, f w| ≤ ∑ᶠ w ∈ S, |f w| := by sorry

alias «GroundTheory».«Heights₂».«Heights».«abs_finsum_mem_le_finsum_mem_abs» := P2M_GroundTheory_Heights__Heights_abs_finsum_mem_le_finsum_mem_abs_db8835e7e74d
