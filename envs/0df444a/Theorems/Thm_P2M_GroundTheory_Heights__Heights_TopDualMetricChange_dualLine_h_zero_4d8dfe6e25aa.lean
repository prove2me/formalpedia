-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_TopDualMetricChange_dualLine_h_zero_4d8dfe6e25aa
-- name    : P2M_GroundTheory_Heights__Heights_TopDualMetricChange_dualLine_h_zero_4d8dfe6e25aa
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T10:50:18.437312+00:00
-- url     : https://prove2.me/theorems/9f219e88-0f1b-527d-886b-8ee891905aaa
-- title:
--   P2 M Ground Theory Heights  Heights Top Dual Metric Change dual Line h zero 4d8dfe6e25aa: P2 M Ground Theory Heights  Heights Top Dual Metric Change dual Line h zero 4d8dfe6e25aa
-- statement:
--   The P2 M Ground Theory Heights  Heights Top Dual Metric Change dual Line h zero 4d8dfe6e25aa construction uses the P2 M Ground Theory Heights  Heights Top Dual Metric Change dual Line h zero 4d8dfe6e25aa property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualTopMetricChange.lean#L25-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualTopMetricChange.lean#L25-L32

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

theorem P2M_GroundTheory_Heights__Heights_TopDualMetricChange_dualLine_h_zero_4d8dfe6e25aa (F : HermLattice K i) (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))) (z : (Σ _ : Unit, T) → ℂ)
    (hz : ¬ ∀ k : Unit, ∃ t, z ⟨k, t⟩ ≠ 0) : (dualLine F b hb).h z = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«TopDualMetricChange».«dualLine_h_zero» := P2M_GroundTheory_Heights__Heights_TopDualMetricChange_dualLine_h_zero_4d8dfe6e25aa
