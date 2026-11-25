-- Prove2me | Theorems.Thm_PI_IwaMeasEx_MG_mulEquivHaarChar_eq_of_chart
-- name    : PI.IwaMeasEx.MG.mulEquivHaarChar_eq_of_chart
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T13:45:28.47432+00:00
-- url     : https://prove2.me/theorems/0a52e947-b7c9-5e81-a3bc-f0c6964c0076
-- title:
--   MG: mul Equiv Haar Char eq of chart
-- statement:
--   The MG construction uses the mul Equiv Haar Char eq of chart property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IwasawaMeasureExistence/MulEquivHaarCharEqOfChart.lean#L29-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IwasawaMeasureExistence/MulEquivHaarCharEqOfChart.lean#L29-L45

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IwasawaMeasureExistence_MulEquivHaarCharEqOfChart
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.IwaMeasEx PI.IwaMeasEx.MG
open MeasureTheory Measure Topology Set
open scoped ENNReal NNReal
variable {G : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G] [BorelSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G]
variable {Y : Type*} [AddCommGroup Y] [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
  [IsTopologicalAddGroup Y] [LocallyCompactSpace Y]

theorem PI.IwaMeasEx.MG.mulEquivHaarChar_eq_of_chart (μ : Measure G) [IsHaarMeasure μ] [Regular μ] (ν : Measure Y)
    [IsAddHaarMeasure ν] [Regular ν] (χ : G → Y) (hχm : Measurable χ) (hχ : μ.map χ = ν) (φ : G ≃ₜ* G)
    (L : Y ≃ₜ+ Y) (h : ∀ x, χ (φ x) = L (χ x)) : mulEquivHaarChar φ = addEquivAddHaarChar L := by sorry
