-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_CurveDegreeVert_sameOrbit_symm_6e2327b721fd
-- name    : P2M_GroundTheory_Heights__Heights_Targets_CurveDegreeVert_sameOrbit_symm_6e2327b721fd
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T04:41:22.209967+00:00
-- url     : https://prove2.me/theorems/17089e71-e821-4317-a09e-890de5ffc2b6
-- title:
--   P2 M Ground Theory Heights  Heights Targets Curve Degree Vert same Orbit symm 6e2327b721fd: P2 M Ground Theory Heights  Heights Targets Curve Degree Vert same Orbit symm 6e2327b721fd
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets Curve Degree Vert same Orbit symm 6e2327b721fd construction uses the P2 M Ground Theory Heights  Heights Targets Curve Degree Vert same Orbit symm 6e2327b721fd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PCurveDegreeVert.lean#L40-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PCurveDegreeVert.lean#L40-L44

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsCurveDegreeVert
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NotIsHorizontalOfDimOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ArithVarZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ExistsIsSheetFinZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PCurveDegreeVert
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
omit [Fintype K] [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_Targets_CurveDegreeVert_sameOrbit_symm_6e2327b721fd {z z' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') : SameOrbit z' z := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«CurveDegreeVert».«sameOrbit_symm» := P2M_GroundTheory_Heights__Heights_Targets_CurveDegreeVert_sameOrbit_symm_6e2327b721fd
