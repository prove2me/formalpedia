-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartMongeAmpereAffineInvariance_fderiv_fderiv_comp_affine_7e54354380f4
-- name    : P2M_GroundTheory_Heights__Heights_ChartMongeAmpereAffineInvariance_fderiv_fderiv_comp_affine_7e54354380f4
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:15:10.466646+00:00
-- url     : https://prove2.me/theorems/8a78a296-e0ac-548c-882e-838a9d2be92b
-- title:
--   P2 M Ground Theory Heights  Heights Chart Monge Ampere Affine Invariance fderiv fderiv comp affine 7e54354380f4: P2 M Ground Theory Heights  Heights Chart Monge Ampere Affine Invariance fderiv fderiv
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Monge Ampere Affine Invariance fderiv fderiv comp affine 7e54354380f4 construction uses the P2 M Ground Theory Heights  Heights Chart Monge Ampere Affine Invariance fderiv fderiv comp affine 7e54354380f4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/ChartMassAffine.lean#L106-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/ChartMassAffine.lean#L106-L121

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

theorem P2M_GroundTheory_Heights__Heights_ChartMongeAmpereAffineInvariance_fderiv_fderiv_comp_affine_7e54354380f4 (φ : (Fin D → ℂ) → ℝ) (c : Fin D → ℂ) (L : (Fin D → ℂ) ≃L[ℝ] (Fin D → ℂ))
    (κ : ℝ) (z u v : Fin D → ℂ) :
    fderiv ℝ (fderiv ℝ fun y => φ (c + L y) + κ) z u v = fderiv ℝ (fderiv ℝ φ) (c + L z) (L u) (L v) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartMongeAmpereAffineInvariance».«fderiv_fderiv_comp_affine» := P2M_GroundTheory_Heights__Heights_ChartMongeAmpereAffineInvariance_fderiv_fderiv_comp_affine_7e54354380f4
