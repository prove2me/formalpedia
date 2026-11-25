-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartIntegrationByPartsSymmetry_continuous_mdisc_bd9e9069925a
-- name    : P2M_GroundTheory_Heights__Heights_ChartIntegrationByPartsSymmetry_continuous_mdisc_bd9e9069925a
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T00:29:17.072436+00:00
-- url     : https://prove2.me/theorems/96973cbb-49d2-4b76-a394-3aab35f71e54
-- title:
--   P2 M Ground Theory Heights  Heights Chart Integration By Parts Symmetry continuous mdisc bd9e9069925a: P2 M Ground Theory Heights  Heights Chart Integration By Parts Symmetry continuous mdisc bd9e9069
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Integration By Parts Symmetry continuous mdisc bd9e9069925a construction uses the P2 M Ground Theory Heights  Heights Chart Integration By Parts Symmetry continuous mdisc bd9e9069925a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/ChartCutoffParts.lean#L151-L155
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/ChartCutoffParts.lean#L151-L155

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_HessCRestrictThm
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsChartCutoffEnergy
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartEnergyCocycle
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartEnergySwap
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ChartCutoffParts
import Theorems.Thm_ReciprocityTheory_AnForm_A_continuous_mdisc

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

theorem P2M_GroundTheory_Heights__Heights_ChartIntegrationByPartsSymmetry_continuous_mdisc_bd9e9069925a {X : Type*} [TopologicalSpace X] {F : X → Fin D → Matrix (Fin D) (Fin D) ℂ}
    (hF : ∀ k, Continuous fun x => F x k) : Continuous fun x => mdisc (F x) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartIntegrationByPartsSymmetry».«continuous_mdisc» := P2M_GroundTheory_Heights__Heights_ChartIntegrationByPartsSymmetry_continuous_mdisc_bd9e9069925a
