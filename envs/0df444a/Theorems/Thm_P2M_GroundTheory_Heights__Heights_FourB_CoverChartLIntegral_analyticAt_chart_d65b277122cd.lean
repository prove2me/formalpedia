-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FourB_CoverChartLIntegral_analyticAt_chart_d65b277122cd
-- name    : P2M_GroundTheory_Heights__Heights_FourB_CoverChartLIntegral_analyticAt_chart_d65b277122cd
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:53:03.907965+00:00
-- url     : https://prove2.me/theorems/6166fc95-6b23-52f7-85ce-7938b7518fa2
-- title:
--   P2 M Ground Theory Heights  Heights Four B Cover Chart LIntegral analytic At chart d65b277122cd: P2 M Ground Theory Heights  Heights Four B Cover Chart LIntegral analytic At chart d65b277122cd
-- statement:
--   The P2 M Ground Theory Heights  Heights Four B Cover Chart LIntegral analytic At chart d65b277122cd construction uses the P2 M Ground Theory Heights  Heights Four B Cover Chart LIntegral analytic At chart d65b277122cd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/PCoverChartLIntegral.lean#L142-L146
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/PCoverChartLIntegral.lean#L142-L146

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_StatementsCoverInt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Degree
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PLCurveA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_PCoverChartLIntegral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FourB
open ReciprocityTheory.AnForm.M MeasureTheory Topology
noncomputable section
open GroundTheory.Heights₂.Heights.FourB.CoverChartLIntegral
variable {e : ℕ} {X : Type} [TopologicalSpace X]

theorem P2M_GroundTheory_Heights__Heights_FourB_CoverChartLIntegral_analyticAt_chart_d65b277122cd {A : FinHolAtlas e X} (j : Fin A.n) {q : X → Fin e → ℂ} {M₀ : Set X}
    (hholo : ∀ i, A.HoloOn M₀ fun x => q x i) {y : Fin e → ℂ}
    (hy : y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' M₀) :
    AnalyticAt ℂ (q ∘ (A.chart j).symm) y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FourB».«CoverChartLIntegral».«analyticAt_chart» := P2M_GroundTheory_Heights__Heights_FourB_CoverChartLIntegral_analyticAt_chart_d65b277122cd
