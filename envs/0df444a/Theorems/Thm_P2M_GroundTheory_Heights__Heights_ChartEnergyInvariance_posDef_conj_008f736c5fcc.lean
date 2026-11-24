-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartEnergyInvariance_posDef_conj_008f736c5fcc
-- name    : P2M_GroundTheory_Heights__Heights_ChartEnergyInvariance_posDef_conj_008f736c5fcc
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:19:49.138414+00:00
-- url     : https://prove2.me/theorems/c46b4da4-0742-41ab-83c8-0c3eb636c790
-- title:
--   P2 M Ground Theory Heights  Heights Chart Energy Invariance pos Def conj 008f736c5fcc: P2 M Ground Theory Heights  Heights Chart Energy Invariance pos Def conj 008f736c5fcc
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Energy Invariance pos Def conj 008f736c5fcc construction uses the P2 M Ground Theory Heights  Heights Chart Energy Invariance pos Def conj 008f736c5fcc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PChartEnergyInvariant.lean#L25-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PChartEnergyInvariant.lean#L25-L28

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsChartEnergyInvariant
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsChartEnergySwap
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ChartMassAffine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartMassInvariant
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartEnergyInvariant
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
open ReciprocityTheory.ChartRestriction.G.Geo Matrix MeasureTheory
open scoped ComplexOrder
noncomputable section
open GroundTheory.Heights₂.Heights.ChartEnergyInvariance
open ChartMongeAmpereAffineInvariance
variable {e : ℕ}

theorem P2M_GroundTheory_Heights__Heights_ChartEnergyInvariance_posDef_conj_008f736c5fcc {M C : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ} (hM : M.PosDef) (hC : C.det ≠ 0) :
    (Cᴴ * M * C).PosDef := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartEnergyInvariance».«posDef_conj» := P2M_GroundTheory_Heights__Heights_ChartEnergyInvariance_posDef_conj_008f736c5fcc
