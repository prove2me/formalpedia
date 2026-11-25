-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Regular_ChartMongeAmpereL1Measure_maMeasure_le_smul_sum_62af3e70de23
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Regular_ChartMongeAmpereL1Measure_maMeasure_le_smul_sum_62af3e70de23
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T14:31:14.066655+00:00
-- url     : https://prove2.me/theorems/4b573de7-3940-43a9-b7cd-3ab8cf54b85a
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Regular Chart Monge Ampere L1 Measure ma Measure le smul sum 62af3e70de23: P2 M Ground Theory Heights  Heights Indefinite Row Side Fu
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Regular Chart Monge Ampere L1 Measure ma Measure le smul sum 62af3e70de23 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Regular Chart Monge Ampere L1 Measure ma Measure le smul sum 62af3e70de23 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/AestronglyMeasurableMapSymm.lean#L177-L269
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/AestronglyMeasurableMapSymm.lean#L177-L269

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Regular_ChartMongeAmpereL1Measure_maMeasure_le_smul_sum_62af3e70de23 {D : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] (A : FinHolAtlas D X) (P : PotentialCharts A)
    (Φ : Fin D → LocPot X) (hΦ : ∀ i, IsPotential A (Φ i)) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧
      maMeasure A Φ ≤ C • ∑ k, (volume.restrict (P.chartMid k)).map (P.chart k).symm := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Regular».«ChartMongeAmpereL1Measure».«maMeasure_le_smul_sum» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Regular_ChartMongeAmpereL1Measure_maMeasure_le_smul_sum_62af3e70de23
