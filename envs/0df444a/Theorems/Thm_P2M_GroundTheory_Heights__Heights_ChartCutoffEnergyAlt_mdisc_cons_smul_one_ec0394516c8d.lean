-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartCutoffEnergyAlt_mdisc_cons_smul_one_ec0394516c8d
-- name    : P2M_GroundTheory_Heights__Heights_ChartCutoffEnergyAlt_mdisc_cons_smul_one_ec0394516c8d
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T00:18:52.924805+00:00
-- url     : https://prove2.me/theorems/67fc04dc-850c-4532-8838-4870c7f8baae
-- title:
--   P2 M Ground Theory Heights  Heights Chart Cutoff Energy Alt mdisc cons smul one ec0394516c8d: P2 M Ground Theory Heights  Heights Chart Cutoff Energy Alt mdisc cons smul one ec0394516c8d
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Cutoff Energy Alt mdisc cons smul one ec0394516c8d construction uses the P2 M Ground Theory Heights  Heights Chart Cutoff Energy Alt mdisc cons smul one ec0394516c8d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PChartCutoffEnergy.lean#L163-L175
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PChartCutoffEnergy.lean#L163-L175

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

theorem P2M_GroundTheory_Heights__Heights_ChartCutoffEnergyAlt_mdisc_cons_smul_one_ec0394516c8d {n : ℕ} (l m : ℂ) :
    mdisc (Fin.cons (l • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ))
      (fun _ : Fin n => m • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)) :
        Fin (n + 1) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) = l * m ^ n := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartCutoffEnergyAlt».«mdisc_cons_smul_one» := P2M_GroundTheory_Heights__Heights_ChartCutoffEnergyAlt_mdisc_cons_smul_one_ec0394516c8d
