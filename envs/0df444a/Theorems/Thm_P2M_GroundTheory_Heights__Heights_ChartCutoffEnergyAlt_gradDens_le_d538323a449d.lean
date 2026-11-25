-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartCutoffEnergyAlt_gradDens_le_d538323a449d
-- name    : P2M_GroundTheory_Heights__Heights_ChartCutoffEnergyAlt_gradDens_le_d538323a449d
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T00:18:50.659341+00:00
-- url     : https://prove2.me/theorems/a224dd9d-be32-4562-abef-8ea0b5bb94c9
-- title:
--   P2 M Ground Theory Heights  Heights Chart Cutoff Energy Alt grad Dens le d538323a449d: P2 M Ground Theory Heights  Heights Chart Cutoff Energy Alt grad Dens le d538323a449d
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Cutoff Energy Alt grad Dens le d538323a449d construction uses the P2 M Ground Theory Heights  Heights Chart Cutoff Energy Alt grad Dens le d538323a449d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PChartCutoffEnergy.lean#L235-L265
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PChartCutoffEnergy.lean#L235-L265

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsChartCutoffEnergy
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartHessCompare
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PHermFormCompare
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartCutoffEnergy
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
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm Matrix MeasureTheory Filter
open scoped ComplexOrder
noncomputable section
open GroundTheory.Heights₂.Heights.ChartCutoffEnergyAlt
open ReciprocityTheory.AnForm.A

theorem P2M_GroundTheory_Heights__Heights_ChartCutoffEnergyAlt_gradDens_le_d538323a449d {n : ℕ} (φ : Fin n → (Fin (n + 1) → ℂ) → ℝ) (v : (Fin (n + 1) → ℂ) → ℝ)
    (y : Fin (n + 1) → ℂ) (hv : DifferentiableAt ℝ v y) (μ : ℝ) (hμ : 0 ≤ μ)
    (hφ : ∀ i, (hessC (φ i) y).PosSemidef ∧
      (((μ : ℝ) : ℂ) • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) - hessC (φ i) y).PosSemidef) :
    gradDens φ v v y ≤
      ((n + 1).factorial : ℝ) * (2 / Real.pi) ^ (n + 1) * ((n + 1) * (‖fderiv ℝ v y‖ ^ 2 * μ ^ n)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartCutoffEnergyAlt».«gradDens_le» := P2M_GroundTheory_Heights__Heights_ChartCutoffEnergyAlt_gradDens_le_d538323a449d
