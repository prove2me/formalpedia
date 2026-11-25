-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Regular_ChartMongeAmpereL1Measure_aestronglyMeasurable_map_symm_b00e7b327fe5
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Regular_ChartMongeAmpereL1Measure_aestronglyMeasurable_map_symm_b00e7b327fe5
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T14:31:16.90081+00:00
-- url     : https://prove2.me/theorems/ad1ef4d4-13a3-4385-a5f6-fa8596c8c30d
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Regular Chart Monge Ampere L1 Measure aestrongly Measurable map symm b00e7b327fe5: P2 M Ground Theory Heights  Heights Indefinite Row
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Regular Chart Monge Ampere L1 Measure aestrongly Measurable map symm b00e7b327fe5 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Regular Chart Monge Ampere L1 Measure aestrongly Measurable map symm b00e7b327fe5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/AestronglyMeasurableMapSymm.lean#L18-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/AestronglyMeasurableMapSymm.lean#L18-L63

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Regular_ChartMongeAmpereL1Measure_aestronglyMeasurable_map_symm_b00e7b327fe5 {D : ℕ} {X : Type} [TopologicalSpace X] [MeasurableSpace X]
    [BorelSpace X] (b : OpenPartialHomeomorph X (Fin D → ℂ)) {M : Set (Fin D → ℂ)}
    (hM : MeasurableSet M) (hMt : M ⊆ b.target) {g : X → ℝ}
    (hg : AEStronglyMeasurable (fun z => g (b.symm z)) (volume.restrict M)) :
    AEStronglyMeasurable g ((volume.restrict M).map b.symm) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Regular».«ChartMongeAmpereL1Measure».«aestronglyMeasurable_map_symm» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Regular_ChartMongeAmpereL1Measure_aestronglyMeasurable_map_symm_b00e7b327fe5
