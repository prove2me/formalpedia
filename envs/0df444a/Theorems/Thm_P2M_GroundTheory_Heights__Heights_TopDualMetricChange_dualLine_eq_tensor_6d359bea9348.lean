-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_TopDualMetricChange_dualLine_eq_tensor_6d359bea9348
-- name    : P2M_GroundTheory_Heights__Heights_TopDualMetricChange_dualLine_eq_tensor_6d359bea9348
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T10:55:53.328927+00:00
-- url     : https://prove2.me/theorems/48c87cf8-2568-413c-9ffe-dc9dc9047c2c
-- title:
--   P2 M Ground Theory Heights  Heights Top Dual Metric Change dual Line eq tensor 6d359bea9348: P2 M Ground Theory Heights  Heights Top Dual Metric Change dual Line eq tensor 6d359bea9348
-- statement:
--   The P2 M Ground Theory Heights  Heights Top Dual Metric Change dual Line eq tensor 6d359bea9348 construction uses the P2 M Ground Theory Heights  Heights Top Dual Metric Change dual Line eq tensor 6d359bea9348 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualTopMetricChange.lean#L61-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualTopMetricChange.lean#L61-L73

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

theorem P2M_GroundTheory_Heights__Heights_TopDualMetricChange_dualLine_eq_tensor_6d359bea9348 (F : HermLattice K i) (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))) :
    dualLine F b hb = (dualLine F.withStdMetric b hb).tensor
      (ReciprocityTheory.ChartRestriction.G.Geo.HermLine.ofWeight (weight F b hb) (weight_hom F b hb)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«TopDualMetricChange».«dualLine_eq_tensor» := P2M_GroundTheory_Heights__Heights_TopDualMetricChange_dualLine_eq_tensor_6d359bea9348
