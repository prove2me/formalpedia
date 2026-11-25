-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartMongeAmpereAffineInvariance_maDensity_comp_affine_974c4adc07ab
-- name    : P2M_GroundTheory_Heights__Heights_ChartMongeAmpereAffineInvariance_maDensity_comp_affine_974c4adc07ab
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:32:20.441175+00:00
-- url     : https://prove2.me/theorems/993f7b33-3ce9-4061-abbb-a0dc41a5ddb1
-- title:
--   P2 M Ground Theory Heights  Heights Chart Monge Ampere Affine Invariance ma Density comp affine 974c4adc07ab: P2 M Ground Theory Heights  Heights Chart Monge Ampere Affine Invariance ma Density comp a
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Monge Ampere Affine Invariance ma Density comp affine 974c4adc07ab construction uses the P2 M Ground Theory Heights  Heights Chart Monge Ampere Affine Invariance ma Density comp affine 974c4adc07ab property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/ChartMassAffine.lean#L155-L163
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/ChartMassAffine.lean#L155-L163

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_IsSemipositiveOn
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ChartMassAffine
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
noncomputable section
open GroundTheory.Heights₂.Heights.ChartMongeAmpereAffineInvariance
variable {D : ℕ}

theorem P2M_GroundTheory_Heights__Heights_ChartMongeAmpereAffineInvariance_maDensity_comp_affine_974c4adc07ab (φ : (Fin D → ℂ) → ℝ) (c : Fin D → ℂ) (P : Matrix (Fin D) (Fin D) ℂ)
    (hP : P.det ≠ 0) (κ : ℝ) (z : Fin D → ℂ) :
    maDensity (fun _ : Fin D => fun y => φ (c + P *ᵥ y) + κ) z =
      Complex.normSq P.det * maDensity (fun _ : Fin D => φ) (c + P *ᵥ z) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartMongeAmpereAffineInvariance».«maDensity_comp_affine» := P2M_GroundTheory_Heights__Heights_ChartMongeAmpereAffineInvariance_maDensity_comp_affine_974c4adc07ab
