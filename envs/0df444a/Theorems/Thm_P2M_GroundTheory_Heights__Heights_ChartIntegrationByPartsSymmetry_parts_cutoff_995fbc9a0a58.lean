-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartIntegrationByPartsSymmetry_parts_cutoff_995fbc9a0a58
-- name    : P2M_GroundTheory_Heights__Heights_ChartIntegrationByPartsSymmetry_parts_cutoff_995fbc9a0a58
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:36:41.673496+00:00
-- url     : https://prove2.me/theorems/5fb3731c-2980-4bbb-8997-830200d008ca
-- title:
--   P2 M Ground Theory Heights  Heights Chart Integration By Parts Symmetry parts cutoff 995fbc9a0a58: P2 M Ground Theory Heights  Heights Chart Integration By Parts Symmetry parts cutoff 995fbc9a0a58
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Integration By Parts Symmetry parts cutoff 995fbc9a0a58 construction uses the P2 M Ground Theory Heights  Heights Chart Integration By Parts Symmetry parts cutoff 995fbc9a0a58 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/ChartCutoffParts.lean#L195-L226
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/ChartCutoffParts.lean#L195-L226

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_HessCRestrictThm
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsChartCutoffEnergy
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartEnergyCocycle
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartEnergySwap
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ChartCutoffParts
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
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A Matrix MeasureTheory Filter Topology
open scoped ComplexOrder
noncomputable section
open GroundTheory.Heights₂.Heights.ChartIntegrationByPartsSymmetry
variable {D : ℕ}

theorem P2M_GroundTheory_Heights__Heights_ChartIntegrationByPartsSymmetry_parts_cutoff_995fbc9a0a58 {n : ℕ} {φ : Fin n → (Fin (n + 1) → ℂ) → ℝ} (hφ : ∀ i, ContDiff ℝ 3 (φ i))
    {ψ u w : (Fin (n + 1) → ℂ) → ℝ} (hψ : ContDiff ℝ 3 ψ) (hψc : HasCompactSupport ψ)
    (hu : ContDiff ℝ 3 u) (hw : ContDiff ℝ 3 w) :
    Integrable (fun y => ψ y * u y * maDens (Fin.cons w φ) y) ∧
      Integrable (fun y => ψ y * gradDens φ u w y) ∧
      Integrable (fun y => u y * gradDens φ ψ w y) ∧
      ∫ y, ψ y * u y * maDens (Fin.cons w φ) y =
        -(∫ y, ψ y * gradDens φ u w y) - ∫ y, u y * gradDens φ ψ w y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartIntegrationByPartsSymmetry».«parts_cutoff» := P2M_GroundTheory_Heights__Heights_ChartIntegrationByPartsSymmetry_parts_cutoff_995fbc9a0a58
