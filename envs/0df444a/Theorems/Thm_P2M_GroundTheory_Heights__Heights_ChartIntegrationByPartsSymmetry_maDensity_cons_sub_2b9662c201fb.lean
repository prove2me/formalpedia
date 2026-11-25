-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartIntegrationByPartsSymmetry_maDensity_cons_sub_2b9662c201fb
-- name    : P2M_GroundTheory_Heights__Heights_ChartIntegrationByPartsSymmetry_maDensity_cons_sub_2b9662c201fb
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T00:33:50.831737+00:00
-- url     : https://prove2.me/theorems/d1eb7eef-c63f-4c53-aebd-6ab2d93964f5
-- title:
--   P2 M Ground Theory Heights  Heights Chart Integration By Parts Symmetry ma Density cons sub 2b9662c201fb: P2 M Ground Theory Heights  Heights Chart Integration By Parts Symmetry ma Density cons sub 2b
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Integration By Parts Symmetry ma Density cons sub 2b9662c201fb construction uses the P2 M Ground Theory Heights  Heights Chart Integration By Parts Symmetry ma Density cons sub 2b9662c201fb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/ChartCutoffParts.lean#L281-L302
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/ChartCutoffParts.lean#L281-L302

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

theorem P2M_GroundTheory_Heights__Heights_ChartIntegrationByPartsSymmetry_maDensity_cons_sub_2b9662c201fb {f g : (Fin (n + 1) → ℂ) → ℝ} (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (φ : Fin n → (Fin (n + 1) → ℂ) → ℝ) (z : Fin (n + 1) → ℂ) :
    maDensity (Fin.cons (fun y => f y - g y) φ) z = maDensity (Fin.cons f φ) z - maDensity (Fin.cons g φ) z := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartIntegrationByPartsSymmetry».«maDensity_cons_sub» := P2M_GroundTheory_Heights__Heights_ChartIntegrationByPartsSymmetry_maDensity_cons_sub_2b9662c201fb
