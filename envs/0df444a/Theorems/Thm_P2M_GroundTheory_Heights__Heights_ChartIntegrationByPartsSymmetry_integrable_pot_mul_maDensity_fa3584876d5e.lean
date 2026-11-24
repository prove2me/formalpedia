-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartIntegrationByPartsSymmetry_integrable_pot_mul_maDensity_fa3584876d5e
-- name    : P2M_GroundTheory_Heights__Heights_ChartIntegrationByPartsSymmetry_integrable_pot_mul_maDensity_fa3584876d5e
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:36:41.70751+00:00
-- url     : https://prove2.me/theorems/96c4837a-2f81-4ba0-9dbe-9818bf7729bf
-- title:
--   P2 M Ground Theory Heights  Heights Chart Integration By Parts Symmetry integrable pot mul ma Density fa3584876d5e: P2 M Ground Theory Heights  Heights Chart Integration By Parts Symmetry integrable p
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Integration By Parts Symmetry integrable pot mul ma Density fa3584876d5e construction uses the P2 M Ground Theory Heights  Heights Chart Integration By Parts Symmetry integrable pot mul ma Density fa3584876d5e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/ChartCutoffParts.lean#L304-L321
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/ChartCutoffParts.lean#L304-L321

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

theorem P2M_GroundTheory_Heights__Heights_ChartIntegrationByPartsSymmetry_integrable_pot_mul_maDensity_fa3584876d5e {A B C D : Matrix (Fin (n + 1 + 1)) (Fin (n + 1 + 1)) ℂ}
    {T : Fin n → Matrix (Fin (n + 1 + 1)) (Fin (n + 1 + 1)) ℂ} (hA : A.PosDef) (hB : B.PosDef) (hC : C.PosDef)
    (hD : D.PosDef) (hT : ∀ i, (T i).PosDef) :
    Integrable (fun y : Fin (n + 1) → ℂ => (hermChartPot A y - hermChartPot B y) *
      maDensity (Fin.cons (fun y' => hermChartPot C y' - hermChartPot D y') fun i => hermChartPot (T i)) y) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartIntegrationByPartsSymmetry».«integrable_pot_mul_maDensity» := P2M_GroundTheory_Heights__Heights_ChartIntegrationByPartsSymmetry_integrable_pot_mul_maDensity_fa3584876d5e
