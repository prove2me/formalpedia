-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartIntegrationByPartsSymmetry_hessC_sub_2ceea7e5a053
-- name    : P2M_GroundTheory_Heights__Heights_ChartIntegrationByPartsSymmetry_hessC_sub_2ceea7e5a053
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T00:28:20.4184+00:00
-- url     : https://prove2.me/theorems/36f65004-386c-4942-a245-6c98438111e2
-- title:
--   P2 M Ground Theory Heights  Heights Chart Integration By Parts Symmetry hess C sub 2ceea7e5a053: P2 M Ground Theory Heights  Heights Chart Integration By Parts Symmetry hess C sub 2ceea7e5a053
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Integration By Parts Symmetry hess C sub 2ceea7e5a053 construction uses the P2 M Ground Theory Heights  Heights Chart Integration By Parts Symmetry hess C sub 2ceea7e5a053 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/ChartCutoffParts.lean#L264-L279
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/ChartCutoffParts.lean#L264-L279

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
variable {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_ChartIntegrationByPartsSymmetry_hessC_sub_2ceea7e5a053 {D : ℕ} {f g : (Fin D → ℂ) → ℝ} (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (z : Fin D → ℂ) :
    hessC (fun y => f y - g y) z = hessC f z - hessC g z := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartIntegrationByPartsSymmetry».«hessC_sub» := P2M_GroundTheory_Heights__Heights_ChartIntegrationByPartsSymmetry_hessC_sub_2ceea7e5a053
