-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_TopDualMetricChange_weight_smooth_7497b1b6e65e
-- name    : P2M_GroundTheory_Heights__Heights_TopDualMetricChange_weight_smooth_7497b1b6e65e
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T11:16:02.589157+00:00
-- url     : https://prove2.me/theorems/1b4292ce-e848-4575-bb52-c00e2fdae42d
-- title:
--   P2 M Ground Theory Heights  Heights Top Dual Metric Change weight smooth 7497b1b6e65e: P2 M Ground Theory Heights  Heights Top Dual Metric Change weight smooth 7497b1b6e65e
-- statement:
--   The P2 M Ground Theory Heights  Heights Top Dual Metric Change weight smooth 7497b1b6e65e construction uses the P2 M Ground Theory Heights  Heights Top Dual Metric Change weight smooth 7497b1b6e65e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualTopMetricChange.lean#L55-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualTopMetricChange.lean#L55-L59

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

theorem P2M_GroundTheory_Heights__Heights_TopDualMetricChange_weight_smooth_7497b1b6e65e (F : HermLattice K i) (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))) : SmoothFn (weight F b hb) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«TopDualMetricChange».«weight_smooth» := P2M_GroundTheory_Heights__Heights_TopDualMetricChange_weight_smooth_7497b1b6e65e
