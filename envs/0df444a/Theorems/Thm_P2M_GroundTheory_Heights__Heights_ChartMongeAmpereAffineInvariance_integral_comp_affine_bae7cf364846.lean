-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartMongeAmpereAffineInvariance_integral_comp_affine_bae7cf364846
-- name    : P2M_GroundTheory_Heights__Heights_ChartMongeAmpereAffineInvariance_integral_comp_affine_bae7cf364846
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T01:32:23.109664+00:00
-- url     : https://prove2.me/theorems/f0816c1a-2509-4c57-8b76-4898609f3f28
-- title:
--   P2 M Ground Theory Heights  Heights Chart Monge Ampere Affine Invariance integral comp affine bae7cf364846: P2 M Ground Theory Heights  Heights Chart Monge Ampere Affine Invariance integral comp affin
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Monge Ampere Affine Invariance integral comp affine bae7cf364846 construction uses the P2 M Ground Theory Heights  Heights Chart Monge Ampere Affine Invariance integral comp affine bae7cf364846 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/ChartMassAffine.lean#L174-L189
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/ChartMassAffine.lean#L174-L189

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

theorem P2M_GroundTheory_Heights__Heights_ChartMongeAmpereAffineInvariance_integral_comp_affine_bae7cf364846 (f : (Fin D → ℂ) → ℝ) (c : Fin D → ℂ) (P : Matrix (Fin D) (Fin D) ℂ)
    (hP : P.det ≠ 0) :
    ∫ y, f (c + P *ᵥ y) = (Complex.normSq P.det)⁻¹ * ∫ y, f y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartMongeAmpereAffineInvariance».«integral_comp_affine» := P2M_GroundTheory_Heights__Heights_ChartMongeAmpereAffineInvariance_integral_comp_affine_bae7cf364846
