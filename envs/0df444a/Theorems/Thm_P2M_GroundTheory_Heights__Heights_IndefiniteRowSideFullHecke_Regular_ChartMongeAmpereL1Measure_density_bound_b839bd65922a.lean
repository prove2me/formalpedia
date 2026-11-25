-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Regular_ChartMongeAmpereL1Measure_density_bound_b839bd65922a
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Regular_ChartMongeAmpereL1Measure_density_bound_b839bd65922a
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T14:29:37.944618+00:00
-- url     : https://prove2.me/theorems/4a81e233-6228-408a-b037-82656ba5d2ad
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Regular Chart Monge Ampere L1 Measure density bound b839bd65922a: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Regular Chart Monge Ampere L1 Measure density bound b839bd65922a construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Regular Chart Monge Ampere L1 Measure density bound b839bd65922a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/AestronglyMeasurableMapSymm.lean#L150-L175
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/AestronglyMeasurableMapSymm.lean#L150-L175

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Regular_ChartMongeAmpereL1Measure_density_bound_b839bd65922a {D : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X]
    (A : FinHolAtlas D X) (Q : ChartPartition A) (Φ : Fin D → LocPot X)
    (hΦ : ∀ i, IsPotential A (Φ i)) (j : Fin A.n) :
    ∃ c : ℝ≥0∞, c ≠ ⊤ ∧ ∀ y ∈ (A.chart j).target,
      ENNReal.ofReal (Q.χ j ((A.chart j).symm y) * locDens A Φ j y) ≤
        (tsupport (Q.χ j)).indicator (fun _ => c) ((A.chart j).symm y) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Regular».«ChartMongeAmpereL1Measure».«density_bound» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Regular_ChartMongeAmpereL1Measure_density_bound_b839bd65922a
