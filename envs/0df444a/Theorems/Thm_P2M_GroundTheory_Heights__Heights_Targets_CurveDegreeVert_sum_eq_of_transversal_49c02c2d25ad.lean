-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_CurveDegreeVert_sum_eq_of_transversal_49c02c2d25ad
-- name    : P2M_GroundTheory_Heights__Heights_Targets_CurveDegreeVert_sum_eq_of_transversal_49c02c2d25ad
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T04:44:00.774936+00:00
-- url     : https://prove2.me/theorems/91c7aefe-3bc2-4d60-acee-21312ad5d18f
-- title:
--   P2 M Ground Theory Heights  Heights Targets Curve Degree Vert sum eq of transversal 49c02c2d25ad: P2 M Ground Theory Heights  Heights Targets Curve Degree Vert sum eq of transversal 49c02c2d25ad
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets Curve Degree Vert sum eq of transversal 49c02c2d25ad construction uses the P2 M Ground Theory Heights  Heights Targets Curve Degree Vert sum eq of transversal 49c02c2d25ad property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PCurveDegreeVert.lean#L55-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PCurveDegreeVert.lean#L55-L72

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

theorem P2M_GroundTheory_Heights__Heights_Targets_CurveDegreeVert_sum_eq_of_transversal_49c02c2d25ad {P : Ideal (MRing ι)} {R R' : Finset ((Σ k, ι k) → ℂ)}
    (hRP : ∀ t ∈ R, t ∈ mcPts P) (hRu : ∀ z ∈ mcPts P, ∃! t, t ∈ R ∧ SameOrbit z t)
    (hR'P : ∀ t ∈ R', t ∈ mcPts P) (hR'u : ∀ z ∈ mcPts P, ∃! t, t ∈ R' ∧ SameOrbit z t)
    (h : ((Σ k, ι k) → ℂ) → ℝ) (hh : ∀ z z', z ∈ mcPts P → SameOrbit z z' → h z = h z') :
    ∑ t ∈ R, h t = ∑ t ∈ R', h t := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«CurveDegreeVert».«sum_eq_of_transversal» := P2M_GroundTheory_Heights__Heights_Targets_CurveDegreeVert_sum_eq_of_transversal_49c02c2d25ad
