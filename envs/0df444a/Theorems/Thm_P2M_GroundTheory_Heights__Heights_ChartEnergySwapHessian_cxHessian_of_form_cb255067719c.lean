-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartEnergySwapHessian_cxHessian_of_form_cb255067719c
-- name    : P2M_GroundTheory_Heights__Heights_ChartEnergySwapHessian_cxHessian_of_form_cb255067719c
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T00:18:20.494529+00:00
-- url     : https://prove2.me/theorems/39023f4e-d758-4c6d-a01d-6e367f0e344a
-- title:
--   P2 M Ground Theory Heights  Heights Chart Energy Swap Hessian cx Hessian of form cb255067719c: P2 M Ground Theory Heights  Heights Chart Energy Swap Hessian cx Hessian of form cb255067719c
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Energy Swap Hessian cx Hessian of form cb255067719c construction uses the P2 M Ground Theory Heights  Heights Chart Energy Swap Hessian cx Hessian of form cb255067719c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/ChartHessHolo.lean#L102-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/ChartHessHolo.lean#L102-L117

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ChartMassAffine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ChartHessHolo
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
open ReciprocityTheory.ChartRestriction.G.Geo Matrix Filter Topology
noncomputable section
open GroundTheory.Heights₂.Heights.ChartEnergySwapHessian
open ChartMongeAmpereAffineInvariance
variable {D : ℕ} {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℂ E'] [NormedSpace ℝ E']
  [IsScalarTower ℝ ℂ E']

theorem P2M_GroundTheory_Heights__Heights_ChartEnergySwapHessian_cxHessian_of_form_cb255067719c (f g : (Fin D → ℂ) → ℝ) (y w : Fin D → ℂ) (L : (Fin D → ℂ) →L[ℂ] (Fin D → ℂ))
    (R : (Fin D → ℂ) → (Fin D → ℂ) → ℝ)
    (hH : ∀ u v, fderiv ℝ (fderiv ℝ f) y u v = fderiv ℝ (fderiv ℝ g) w (L u) (L v) + R u v)
    (hR₁ : ∀ u v, R (Complex.I • u) (Complex.I • v) = -R u v)
    (hR₂ : ∀ u v, R u (Complex.I • v) = R (Complex.I • u) v) :
    cxHessian f y = (LinearMap.toMatrix' (L : (Fin D → ℂ) →ₗ[ℂ] (Fin D → ℂ)))ᵀ * cxHessian g w *
      (LinearMap.toMatrix' (L : (Fin D → ℂ) →ₗ[ℂ] (Fin D → ℂ))).map (starRingEnd ℂ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartEnergySwapHessian».«cxHessian_of_form» := P2M_GroundTheory_Heights__Heights_ChartEnergySwapHessian_cxHessian_of_form_cb255067719c
