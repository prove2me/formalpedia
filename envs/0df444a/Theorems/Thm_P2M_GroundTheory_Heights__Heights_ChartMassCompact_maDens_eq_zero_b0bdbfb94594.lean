-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartMassCompact_maDens_eq_zero_b0bdbfb94594
-- name    : P2M_GroundTheory_Heights__Heights_ChartMassCompact_maDens_eq_zero_b0bdbfb94594
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:46:14.334565+00:00
-- url     : https://prove2.me/theorems/03affa1a-7392-4989-a815-06393f8711d3
-- title:
--   P2 M Ground Theory Heights  Heights Chart Mass Compact ma Dens eq zero b0bdbfb94594: P2 M Ground Theory Heights  Heights Chart Mass Compact ma Dens eq zero b0bdbfb94594
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Mass Compact ma Dens eq zero b0bdbfb94594 construction uses the P2 M Ground Theory Heights  Heights Chart Mass Compact ma Dens eq zero b0bdbfb94594 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PChartMassCompact.lean#L40-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PChartMassCompact.lean#L40-L55

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StChartMassCompact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StChartMassCompare
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFibreBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetSumMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCutOff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PChartMassCompact
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
open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ENNReal
noncomputable section
open GroundTheory.Heights₂.Heights.ChartMassCompact
variable {n d : ℕ}

theorem P2M_GroundTheory_Heights__Heights_ChartMassCompact_maDens_eq_zero_b0bdbfb94594 {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ}
    {x : Fin n → ℂ} {s : (Fin d → ℂ) → Fin n → ℂ} (hs : IsSheetAt J A x s)
    (ψ : Fin d → (Fin n → ℂ) → ℝ) (i : Fin d) (hx : x ∉ tsupport (ψ i)) :
    ReciprocityTheory.AnForm.maDens (fun k => ψ k ∘ s) (A *ᵥ x) = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartMassCompact».«maDens_eq_zero» := P2M_GroundTheory_Heights__Heights_ChartMassCompact_maDens_eq_zero_b0bdbfb94594
