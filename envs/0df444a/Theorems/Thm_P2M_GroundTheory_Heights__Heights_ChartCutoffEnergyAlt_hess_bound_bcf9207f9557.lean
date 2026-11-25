-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartCutoffEnergyAlt_hess_bound_bcf9207f9557
-- name    : P2M_GroundTheory_Heights__Heights_ChartCutoffEnergyAlt_hess_bound_bcf9207f9557
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T00:18:57.725935+00:00
-- url     : https://prove2.me/theorems/bf7c699c-0f36-461a-ba7b-7454daa26490
-- title:
--   P2 M Ground Theory Heights  Heights Chart Cutoff Energy Alt hess bound bcf9207f9557: P2 M Ground Theory Heights  Heights Chart Cutoff Energy Alt hess bound bcf9207f9557
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Cutoff Energy Alt hess bound bcf9207f9557 construction uses the P2 M Ground Theory Heights  Heights Chart Cutoff Energy Alt hess bound bcf9207f9557 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PChartCutoffEnergy.lean#L191-L233
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PChartCutoffEnergy.lean#L191-L233

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

theorem P2M_GroundTheory_Heights__Heights_ChartCutoffEnergyAlt_hess_bound_bcf9207f9557 {e : ℕ} {M : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ} (hM : M.PosDef) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : Fin e → ℂ, (hessC (hermChartPot M) y).PosSemidef ∧
      ((((C / (1 + sqn y)) : ℝ) : ℂ) • (1 : Matrix (Fin e) (Fin e) ℂ) - hessC (hermChartPot M) y).PosSemidef := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartCutoffEnergyAlt».«hess_bound» := P2M_GroundTheory_Heights__Heights_ChartCutoffEnergyAlt_hess_bound_bcf9207f9557
