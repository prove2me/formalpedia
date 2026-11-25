-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_CutOffBoundaryBound_term_bound_3573df0163f5
-- name    : P2M_GroundTheory_Heights__Heights_CutOffBoundaryBound_term_bound_3573df0163f5
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:58:30.835155+00:00
-- url     : https://prove2.me/theorems/74d23d0d-8766-4800-8226-394cd0aa572a
-- title:
--   P2 M Ground Theory Heights  Heights Cut Off Boundary Bound term bound 3573df0163f5: P2 M Ground Theory Heights  Heights Cut Off Boundary Bound term bound 3573df0163f5
-- statement:
--   The P2 M Ground Theory Heights  Heights Cut Off Boundary Bound term bound 3573df0163f5 construction uses the P2 M Ground Theory Heights  Heights Cut Off Boundary Bound term bound 3573df0163f5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PCutOffBoundaryBound.lean#L135-L154
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PCutOffBoundaryBound.lean#L135-L154

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCutOffBoundaryBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCutOffBoundaryParts
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StChartMassCompact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetSumMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCutOff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCutOffGradient
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_OsgoodSeparate
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_LocDens
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCutOffBoundaryBound
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
open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open scoped ContDiff
noncomputable section
open GroundTheory.Heights₂.Heights.CutOffBoundaryBound
variable {n d : ℕ}

theorem P2M_GroundTheory_Heights__Heights_CutOffBoundaryBound_term_bound_3573df0163f5 {G F χ mF mχ g₁ g₂ Eχ EF M C t : ℝ} (ht : 0 < t) (hC : 0 ≤ C) (hM : |G * F| ≤ M)
    (hEχ : 0 ≤ Eχ) (hEF : 0 ≤ EF) (h₁ : |g₁| ≤ C * √Eχ * √EF) (h₂ : |g₂| ≤ C * √EF * √Eχ) :
    |G * (χ * mF + F * mχ + g₁ + g₂) - χ * G * mF| ≤
      M * |1 * mχ| + C * t * (1 * Eχ) + C / t * (G ^ 2 * EF) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«CutOffBoundaryBound».«term_bound» := P2M_GroundTheory_Heights__Heights_CutOffBoundaryBound_term_bound_3573df0163f5
