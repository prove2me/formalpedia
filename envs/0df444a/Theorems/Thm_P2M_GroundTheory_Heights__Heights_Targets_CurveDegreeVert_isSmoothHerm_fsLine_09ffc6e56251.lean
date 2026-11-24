-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_CurveDegreeVert_isSmoothHerm_fsLine_09ffc6e56251
-- name    : P2M_GroundTheory_Heights__Heights_Targets_CurveDegreeVert_isSmoothHerm_fsLine_09ffc6e56251
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:52:34.455602+00:00
-- url     : https://prove2.me/theorems/1b1c1f04-5249-48bb-b43c-5495e50d58be
-- title:
--   P2 M Ground Theory Heights  Heights Targets Curve Degree Vert is Smooth Herm fs Line 09ffc6e56251: P2 M Ground Theory Heights  Heights Targets Curve Degree Vert is Smooth Herm fs Line 09ffc6e56251
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets Curve Degree Vert is Smooth Herm fs Line 09ffc6e56251 construction uses the P2 M Ground Theory Heights  Heights Targets Curve Degree Vert is Smooth Herm fs Line 09ffc6e56251 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PCurveDegreeVert.lean#L21-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PCurveDegreeVert.lean#L21-L33

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsCurveDegreeVert
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NotIsHorizontalOfDimOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ArithVarZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ExistsIsSheetFinZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PCurveDegreeVert
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_isSmoothHerm_fsLine_27a26231cd0b

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 GroundTheory.Heights₂.Heights.Inter
noncomputable section
open GroundTheory.Heights₂.Heights.Targets.CurveDegreeVert
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_Targets_CurveDegreeVert_isSmoothHerm_fsLine_09ffc6e56251 (b : K → ℕ) : IsSmoothHerm (fsLine b : HermLine ι) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«CurveDegreeVert».«isSmoothHerm_fsLine» := P2M_GroundTheory_Heights__Heights_Targets_CurveDegreeVert_isSmoothHerm_fsLine_09ffc6e56251
