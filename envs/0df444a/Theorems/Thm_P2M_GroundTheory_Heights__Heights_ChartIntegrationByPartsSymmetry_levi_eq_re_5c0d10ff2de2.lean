-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartIntegrationByPartsSymmetry_levi_eq_re_5c0d10ff2de2
-- name    : P2M_GroundTheory_Heights__Heights_ChartIntegrationByPartsSymmetry_levi_eq_re_5c0d10ff2de2
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T00:29:31.345867+00:00
-- url     : https://prove2.me/theorems/5a804a08-ff86-49cb-a49d-c4458abdf541
-- title:
--   P2 M Ground Theory Heights  Heights Chart Integration By Parts Symmetry levi eq re 5c0d10ff2de2: P2 M Ground Theory Heights  Heights Chart Integration By Parts Symmetry levi eq re 5c0d10ff2de2
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Integration By Parts Symmetry levi eq re 5c0d10ff2de2 construction uses the P2 M Ground Theory Heights  Heights Chart Integration By Parts Symmetry levi eq re 5c0d10ff2de2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/ChartCutoffParts.lean#L35-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/ChartCutoffParts.lean#L35-L42

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
variable {e : ℕ}

theorem P2M_GroundTheory_Heights__Heights_ChartIntegrationByPartsSymmetry_levi_eq_re_5c0d10ff2de2 (φ : (Fin e → ℂ) → ℝ) (z ξ : Fin e → ℂ) :
    levi φ z ξ = (star (star ξ) ⬝ᵥ (hessC φ z *ᵥ star ξ)).re := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartIntegrationByPartsSymmetry».«levi_eq_re» := P2M_GroundTheory_Heights__Heights_ChartIntegrationByPartsSymmetry_levi_eq_re_5c0d10ff2de2
