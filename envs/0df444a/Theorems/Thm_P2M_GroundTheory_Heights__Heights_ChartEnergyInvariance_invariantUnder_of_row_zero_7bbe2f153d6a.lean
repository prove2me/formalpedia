-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartEnergyInvariance_invariantUnder_of_row_zero_7bbe2f153d6a
-- name    : P2M_GroundTheory_Heights__Heights_ChartEnergyInvariance_invariantUnder_of_row_zero_7bbe2f153d6a
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:19:56.042847+00:00
-- url     : https://prove2.me/theorems/c0e1adb6-5821-4b51-bb7e-b6c46e23982d
-- title:
--   P2 M Ground Theory Heights  Heights Chart Energy Invariance invariant Under of row zero 7bbe2f153d6a: P2 M Ground Theory Heights  Heights Chart Energy Invariance invariant Under of row zero 7bbe2f153d
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Energy Invariance invariant Under of row zero 7bbe2f153d6a construction uses the P2 M Ground Theory Heights  Heights Chart Energy Invariance invariant Under of row zero 7bbe2f153d6a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PChartEnergyInvariant.lean#L58-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PChartEnergyInvariant.lean#L58-L86

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

theorem P2M_GroundTheory_Heights__Heights_ChartEnergyInvariance_invariantUnder_of_row_zero_7bbe2f153d6a (T : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ) (hT : ∀ j : Fin e, T 0 j.succ = 0)
    (hdet : T.det ≠ 0) : EnergyInvariantUnder T := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartEnergyInvariance».«invariantUnder_of_row_zero» := P2M_GroundTheory_Heights__Heights_ChartEnergyInvariance_invariantUnder_of_row_zero_7bbe2f153d6a
