-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartEnergyIntegrableAlt_abs_maDensity_mix_le_da79b66fc811
-- name    : P2M_GroundTheory_Heights__Heights_ChartEnergyIntegrableAlt_abs_maDensity_mix_le_da79b66fc811
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T00:23:24.746838+00:00
-- url     : https://prove2.me/theorems/75953e42-3e2b-4453-bd8c-2d87698a7131
-- title:
--   P2 M Ground Theory Heights  Heights Chart Energy Integrable Alt abs ma Density mix le da79b66fc811: P2 M Ground Theory Heights  Heights Chart Energy Integrable Alt abs ma Density mix le da79b66fc811
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Energy Integrable Alt abs ma Density mix le da79b66fc811 construction uses the P2 M Ground Theory Heights  Heights Chart Energy Integrable Alt abs ma Density mix le da79b66fc811 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PChartEnergyIntegrable.lean#L52-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PChartEnergyIntegrable.lean#L52-L100

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ADensStBA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsChartEnergyIntegrable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsHermFormCompare
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsChartHessCompare
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartDensityIntegrable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartEnergyIntegrable
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
open ReciprocityTheory.ChartRestriction.G.Geo Matrix MeasureTheory Filter
open scoped ComplexOrder
noncomputable section
open GroundTheory.Heights₂.Heights.ChartEnergyIntegrableAlt

theorem P2M_GroundTheory_Heights__Heights_ChartEnergyIntegrableAlt_abs_maDensity_mix_le_da79b66fc811 {e : ℕ} {M N : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ} (k : ℕ) (C : ℝ) (y : Fin e → ℂ)
    (hMp : (cxHessian (hermChartPot M) y).PosSemidef) (hNp : (cxHessian (hermChartPot N) y).PosSemidef)
    (hle : ((C : ℂ) • cxHessian (hermChartPot N) y - cxHessian (hermChartPot M) y).PosSemidef) :
    ‖maDensity (fun j : Fin e => if (j : ℕ) < k then hermChartPot M else hermChartPot N) y‖ ≤
      max C 1 ^ e * maDensity (fun _ : Fin e => hermChartPot N) y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartEnergyIntegrableAlt».«abs_maDensity_mix_le» := P2M_GroundTheory_Heights__Heights_ChartEnergyIntegrableAlt_abs_maDensity_mix_le_da79b66fc811
