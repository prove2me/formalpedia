-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PtsIntegralPoints_segre_ne_zero_291e8e330c27
-- name    : P2M_GroundTheory_Heights__Heights_PtsIntegralPoints_segre_ne_zero_291e8e330c27
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T16:58:43.331431+00:00
-- url     : https://prove2.me/theorems/34da878a-1d96-5cad-bc4c-8c78cf0c9831
-- title:
--   P2 M Ground Theory Heights  Heights Pts Integral Points segre ne zero 291e8e330c27: P2 M Ground Theory Heights  Heights Pts Integral Points segre ne zero 291e8e330c27
-- statement:
--   The P2 M Ground Theory Heights  Heights Pts Integral Points segre ne zero 291e8e330c27 construction uses the P2 M Ground Theory Heights  Heights Pts Integral Points segre ne zero 291e8e330c27 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/PPtsIntegralPoints.lean#L33-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/PPtsIntegralPoints.lean#L33-L38

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightPtsIntegralPoints
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitCurve
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeB
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_PPtsIntegralPoints
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
open ReciprocityTheory.ChartRestriction.G MeasureTheory
open GroundTheory.Heights₂.Heights.PtsIntegralPoints
set_option linter.unusedSectionVars false
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_PtsIntegralPoints_segre_ne_zero_291e8e330c27 {z : (Σ k, ι k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) : Geo.segre z ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PtsIntegralPoints».«segre_ne_zero» := P2M_GroundTheory_Heights__Heights_PtsIntegralPoints_segre_ne_zero_291e8e330c27
