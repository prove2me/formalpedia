-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_TopDualMetricChange_ptsIntegral_neg_f3372bd7f2ce
-- name    : P2M_GroundTheory_Heights__Heights_TopDualMetricChange_ptsIntegral_neg_f3372bd7f2ce
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T11:06:13.212089+00:00
-- url     : https://prove2.me/theorems/c588e910-33a7-5b7c-b8cd-21fd31965c4c
-- title:
--   P2 M Ground Theory Heights  Heights Top Dual Metric Change pts Integral neg f3372bd7f2ce: P2 M Ground Theory Heights  Heights Top Dual Metric Change pts Integral neg f3372bd7f2ce
-- statement:
--   The P2 M Ground Theory Heights  Heights Top Dual Metric Change pts Integral neg f3372bd7f2ce construction uses the P2 M Ground Theory Heights  Heights Top Dual Metric Change pts Integral neg f3372bd7f2ce property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualTopMetricChange.lean#L75-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualTopMetricChange.lean#L75-L86

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

theorem P2M_GroundTheory_Heights__Heights_TopDualMetricChange_ptsIntegral_neg_f3372bd7f2ce {κ : Type} [Fintype κ] {ι : κ → Type} [∀ k, Fintype (ι k)] {e : ℕ}
    (P : Ideal (MRing ι)) (φ : Fin e → ((Σ k, ι k) → ℂ) → ℝ) (g : ((Σ k, ι k) → ℂ) → ℝ) :
    ptsIntegral P φ (fun z => -g z) = -ptsIntegral P φ g := by sorry

alias «GroundTheory».«Heights₂».«Heights».«TopDualMetricChange».«ptsIntegral_neg» := P2M_GroundTheory_Heights__Heights_TopDualMetricChange_ptsIntegral_neg_f3372bd7f2ce
