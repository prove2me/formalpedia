-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_TopDualMetricChange_degree_withStdMetric_sub_d27e90f4ad26
-- name    : P2M_GroundTheory_Heights__Heights_TopDualMetricChange_degree_withStdMetric_sub_d27e90f4ad26
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T10:50:10.994188+00:00
-- url     : https://prove2.me/theorems/da90f9dc-8d58-5a33-9e29-64dfddc0060e
-- title:
--   P2 M Ground Theory Heights  Heights Top Dual Metric Change degree with Std Metric sub d27e90f4ad26: P2 M Ground Theory Heights  Heights Top Dual Metric Change degree with Std Metric sub d27e90f4ad26
-- statement:
--   The P2 M Ground Theory Heights  Heights Top Dual Metric Change degree with Std Metric sub d27e90f4ad26 construction uses the P2 M Ground Theory Heights  Heights Top Dual Metric Change degree with Std Metric sub d27e90f4ad26 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualTopMetricChange.lean#L88-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualTopMetricChange.lean#L88-L92

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ScaledExample
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsDualEnergy
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualLineSemipositive
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualArithVar
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PCoordConeArithVar
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PIntDomainDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ReMulOfPos
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualTopMetricChange
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
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 NumberField
noncomputable section
open GroundTheory.Heights₂.Heights.TopDualMetricChange
variable {K : Type} [Field K] [NumberField K] {i : ℕ} {T : Type} [Fintype T] [DecidableEq T]

theorem P2M_GroundTheory_Heights__Heights_TopDualMetricChange_degree_withStdMetric_sub_d27e90f4ad26 (F : HermLattice K i) :
    F.withStdMetric.degree - F.degree = 1 / 2 * ∑ σ : K →+* ℂ, Real.log (F.metric σ).det.re := by sorry

alias «GroundTheory».«Heights₂».«Heights».«TopDualMetricChange».«degree_withStdMetric_sub» := P2M_GroundTheory_Heights__Heights_TopDualMetricChange_degree_withStdMetric_sub_d27e90f4ad26
