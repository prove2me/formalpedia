-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartEnergyInvariance_invariantUnder_of_row_one_631ce3204412
-- name    : P2M_GroundTheory_Heights__Heights_ChartEnergyInvariance_invariantUnder_of_row_one_631ce3204412
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T00:18:43.008716+00:00
-- url     : https://prove2.me/theorems/18ab8921-dabb-4d8e-a655-c3d764463f37
-- title:
--   P2 M Ground Theory Heights  Heights Chart Energy Invariance invariant Under of row one 631ce3204412: P2 M Ground Theory Heights  Heights Chart Energy Invariance invariant Under of row one 631ce3204412
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Energy Invariance invariant Under of row one 631ce3204412 construction uses the P2 M Ground Theory Heights  Heights Chart Energy Invariance invariant Under of row one 631ce3204412 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PChartEnergyInvariant.lean#L88-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PChartEnergyInvariant.lean#L88-L125

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

theorem P2M_GroundTheory_Heights__Heights_ChartEnergyInvariance_invariantUnder_of_row_one_631ce3204412 (hS : ChartEnergySwapInvariant.Statement)
    (C : Matrix (Fin (e + 1 + 1)) (Fin (e + 1 + 1)) ℂ) (hC : C.det ≠ 0) (h1 : C 0 1 ≠ 0) :
    EnergyInvariantUnder C := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartEnergyInvariance».«invariantUnder_of_row_one» := P2M_GroundTheory_Heights__Heights_ChartEnergyInvariance_invariantUnder_of_row_one_631ce3204412
