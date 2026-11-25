-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartEnergyIntegrableAlt_pot_sub_bound_9147d7c74cf7
-- name    : P2M_GroundTheory_Heights__Heights_ChartEnergyIntegrableAlt_pot_sub_bound_9147d7c74cf7
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:10:48.246404+00:00
-- url     : https://prove2.me/theorems/4848b545-11dc-4190-a86e-6939246acad3
-- title:
--   P2 M Ground Theory Heights  Heights Chart Energy Integrable Alt pot sub bound 9147d7c74cf7: P2 M Ground Theory Heights  Heights Chart Energy Integrable Alt pot sub bound 9147d7c74cf7
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Energy Integrable Alt pot sub bound 9147d7c74cf7 construction uses the P2 M Ground Theory Heights  Heights Chart Energy Integrable Alt pot sub bound 9147d7c74cf7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PChartEnergyIntegrable.lean#L35-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PChartEnergyIntegrable.lean#L35-L50

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

theorem P2M_GroundTheory_Heights__Heights_ChartEnergyIntegrableAlt_pot_sub_bound_9147d7c74cf7 (hCmp : HermFormCompare.Statement) {e : ℕ} {M N : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ}
    (hM : M.PosDef) (hN : N.PosDef) :
    ∃ K : ℝ, ∀ y : Fin e → ℂ, ‖hermChartPot M y - hermChartPot N y‖ ≤ K := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartEnergyIntegrableAlt».«pot_sub_bound» := P2M_GroundTheory_Heights__Heights_ChartEnergyIntegrableAlt_pot_sub_bound_9147d7c74cf7
