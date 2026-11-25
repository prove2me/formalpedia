-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartIntegrationByPartsSymmetry_continuous_hessC_1e95fbef5f3e
-- name    : P2M_GroundTheory_Heights__Heights_ChartIntegrationByPartsSymmetry_continuous_hessC_1e95fbef5f3e
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T00:28:00.923721+00:00
-- url     : https://prove2.me/theorems/9bc784cb-9455-4b98-be21-57b093e62376
-- title:
--   P2 M Ground Theory Heights  Heights Chart Integration By Parts Symmetry continuous hess C 1e95fbef5f3e: P2 M Ground Theory Heights  Heights Chart Integration By Parts Symmetry continuous hess C 1e95fb
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Integration By Parts Symmetry continuous hess C 1e95fbef5f3e construction uses the P2 M Ground Theory Heights  Heights Chart Integration By Parts Symmetry continuous hess C 1e95fbef5f3e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/ChartCutoffParts.lean#L157-L164
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/ChartCutoffParts.lean#L157-L164

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

theorem P2M_GroundTheory_Heights__Heights_ChartIntegrationByPartsSymmetry_continuous_hessC_1e95fbef5f3e {φ : (Fin D → ℂ) → ℝ} (hφ : ContDiff ℝ 2 φ) : Continuous (hessC φ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartIntegrationByPartsSymmetry».«continuous_hessC» := P2M_GroundTheory_Heights__Heights_ChartIntegrationByPartsSymmetry_continuous_hessC_1e95fbef5f3e
