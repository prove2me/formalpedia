-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartEnergyInvariance_conj_mul_4305321ef65a
-- name    : P2M_GroundTheory_Heights__Heights_ChartEnergyInvariance_conj_mul_4305321ef65a
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:19:51.900175+00:00
-- url     : https://prove2.me/theorems/c6bc0098-3667-41b3-bded-83dce26f4b7b
-- title:
--   P2 M Ground Theory Heights  Heights Chart Energy Invariance conj mul 4305321ef65a: P2 M Ground Theory Heights  Heights Chart Energy Invariance conj mul 4305321ef65a
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Energy Invariance conj mul 4305321ef65a construction uses the P2 M Ground Theory Heights  Heights Chart Energy Invariance conj mul 4305321ef65a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PChartEnergyInvariant.lean#L30-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PChartEnergyInvariant.lean#L30-L32

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

theorem P2M_GroundTheory_Heights__Heights_ChartEnergyInvariance_conj_mul_4305321ef65a (M A B : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ) :
    (A * B)ᴴ * M * (A * B) = Bᴴ * (Aᴴ * M * A) * B := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartEnergyInvariance».«conj_mul» := P2M_GroundTheory_Heights__Heights_ChartEnergyInvariance_conj_mul_4305321ef65a
