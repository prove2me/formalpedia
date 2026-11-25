-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartEnergyInvariance_maDensity_comp_affine_family_a2bd3164b5d2
-- name    : P2M_GroundTheory_Heights__Heights_ChartEnergyInvariance_maDensity_comp_affine_family_a2bd3164b5d2
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T00:18:16.656014+00:00
-- url     : https://prove2.me/theorems/059c2477-06c7-4c64-af8d-8db613bb68b8
-- title:
--   P2 M Ground Theory Heights  Heights Chart Energy Invariance ma Density comp affine family a2bd3164b5d2: P2 M Ground Theory Heights  Heights Chart Energy Invariance ma Density comp affine family a2bd31
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Energy Invariance ma Density comp affine family a2bd3164b5d2 construction uses the P2 M Ground Theory Heights  Heights Chart Energy Invariance ma Density comp affine family a2bd3164b5d2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PChartEnergyInvariant.lean#L45-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PChartEnergyInvariant.lean#L45-L56

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

theorem P2M_GroundTheory_Heights__Heights_ChartEnergyInvariance_maDensity_comp_affine_family_a2bd3164b5d2 {D : ℕ} (φ : Fin D → (Fin D → ℂ) → ℝ) (c : Fin D → ℂ)
    (P : Matrix (Fin D) (Fin D) ℂ) (hP : P.det ≠ 0) (κ : ℝ) (z : Fin D → ℂ) :
    maDensity (fun j => fun y => φ j (c + P *ᵥ y) + κ) z =
      Complex.normSq P.det * maDensity φ (c + P *ᵥ z) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartEnergyInvariance».«maDensity_comp_affine_family» := P2M_GroundTheory_Heights__Heights_ChartEnergyInvariance_maDensity_comp_affine_family_a2bd3164b5d2
