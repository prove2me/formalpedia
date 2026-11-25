-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_CutOffBoundaryBound_maDens_cons_eq_zero_7292b531e842
-- name    : P2M_GroundTheory_Heights__Heights_CutOffBoundaryBound_maDens_cons_eq_zero_7292b531e842
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:18:02.490677+00:00
-- url     : https://prove2.me/theorems/6bbe3fbb-2e55-435a-8a41-a3c1c32b9f2b
-- title:
--   P2 M Ground Theory Heights  Heights Cut Off Boundary Bound ma Dens cons eq zero 7292b531e842: P2 M Ground Theory Heights  Heights Cut Off Boundary Bound ma Dens cons eq zero 7292b531e842
-- statement:
--   The P2 M Ground Theory Heights  Heights Cut Off Boundary Bound ma Dens cons eq zero 7292b531e842 construction uses the P2 M Ground Theory Heights  Heights Cut Off Boundary Bound ma Dens cons eq zero 7292b531e842 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PCutOffBoundaryBound.lean#L36-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PCutOffBoundaryBound.lean#L36-L42

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

theorem P2M_GroundTheory_Heights__Heights_CutOffBoundaryBound_maDens_cons_eq_zero_7292b531e842 {D : ℕ} (f : (Fin (D + 1) → ℂ) → ℝ) (ψ : Fin D → (Fin (D + 1) → ℂ) → ℝ)
    (y : Fin (D + 1) → ℂ) (h : f =ᶠ[𝓝 y] fun _ => 0) : maDens (Fin.cons f ψ) y = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«CutOffBoundaryBound».«maDens_cons_eq_zero» := P2M_GroundTheory_Heights__Heights_CutOffBoundaryBound_maDens_cons_eq_zero_7292b531e842
