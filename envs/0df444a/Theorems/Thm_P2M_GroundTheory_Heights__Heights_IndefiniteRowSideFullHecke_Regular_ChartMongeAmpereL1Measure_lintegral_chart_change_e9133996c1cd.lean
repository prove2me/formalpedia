-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Regular_ChartMongeAmpereL1Measure_lintegral_chart_change_e9133996c1cd
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Regular_ChartMongeAmpereL1Measure_lintegral_chart_change_e9133996c1cd
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T14:30:27.398824+00:00
-- url     : https://prove2.me/theorems/8f9621e5-ac95-485b-b3d0-179776d4c317
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Regular Chart Monge Ampere L1 Measure lintegral chart change e9133996c1cd: P2 M Ground Theory Heights  Heights Indefinite Row Side Fu
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Regular Chart Monge Ampere L1 Measure lintegral chart change e9133996c1cd construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Regular Chart Monge Ampere L1 Measure lintegral chart change e9133996c1cd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/AestronglyMeasurableMapSymm.lean#L65-L148
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/AestronglyMeasurableMapSymm.lean#L65-L148

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_ChartMongeAmpereL1Hypotheses
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_MaMeasureB
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_AestronglyMeasurableMapSymm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular
open MeasureTheory Filter Topology Set
open scoped ENNReal
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential IsPosPot maMeasure ChartPartition locDens)
open GroundTheory.Heights₂.Heights.Regular (PotentialCharts)
noncomputable section
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular.ChartMongeAmpereL1Measure

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Regular_ChartMongeAmpereL1Measure_lintegral_chart_change_e9133996c1cd {D : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X]
    (a b : OpenPartialHomeomorph X (Fin D → ℂ))
    (hab : AnalyticOnNhd ℂ (a ∘ b.symm) (b.target ∩ b.symm ⁻¹' a.source))
    {K M : Set X} (hK : IsClosed K) (hKa : K ⊆ a.source) (hM : IsOpen M)
    (hMb : closure M ⊆ b.source) :
    ∃ B : ℝ≥0∞, B ≠ ⊤ ∧ ∀ F : X → ℝ≥0∞,
      ∫⁻ y in a.target, (K ∩ M).indicator F (a.symm y) ≤
        B * ∫⁻ z in b.target ∩ b.symm ⁻¹' M, F (b.symm z) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Regular».«ChartMongeAmpereL1Measure».«lintegral_chart_change» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Regular_ChartMongeAmpereL1Measure_lintegral_chart_change_e9133996c1cd
