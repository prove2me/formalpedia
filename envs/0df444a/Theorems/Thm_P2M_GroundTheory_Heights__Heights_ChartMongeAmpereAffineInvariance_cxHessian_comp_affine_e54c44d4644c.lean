-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartMongeAmpereAffineInvariance_cxHessian_comp_affine_e54c44d4644c
-- name    : P2M_GroundTheory_Heights__Heights_ChartMongeAmpereAffineInvariance_cxHessian_comp_affine_e54c44d4644c
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T01:32:06.189897+00:00
-- url     : https://prove2.me/theorems/f12d281a-d85c-4f9a-89ae-e4f23edc6b1b
-- title:
--   P2 M Ground Theory Heights  Heights Chart Monge Ampere Affine Invariance cx Hessian comp affine e54c44d4644c: P2 M Ground Theory Heights  Heights Chart Monge Ampere Affine Invariance cx Hessian comp a
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Monge Ampere Affine Invariance cx Hessian comp affine e54c44d4644c construction uses the P2 M Ground Theory Heights  Heights Chart Monge Ampere Affine Invariance cx Hessian comp affine e54c44d4644c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/ChartMassAffine.lean#L123-L144
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/ChartMassAffine.lean#L123-L144

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

theorem P2M_GroundTheory_Heights__Heights_ChartMongeAmpereAffineInvariance_cxHessian_comp_affine_e54c44d4644c (φ : (Fin D → ℂ) → ℝ) (c : Fin D → ℂ) (P : Matrix (Fin D) (Fin D) ℂ)
    (hP : P.det ≠ 0) (κ : ℝ) (z : Fin D → ℂ) :
    cxHessian (fun y => φ (c + P *ᵥ y) + κ) z =
      Pᵀ * cxHessian φ (c + P *ᵥ z) * P.map (starRingEnd ℂ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartMongeAmpereAffineInvariance».«cxHessian_comp_affine» := P2M_GroundTheory_Heights__Heights_ChartMongeAmpereAffineInvariance_cxHessian_comp_affine_e54c44d4644c
