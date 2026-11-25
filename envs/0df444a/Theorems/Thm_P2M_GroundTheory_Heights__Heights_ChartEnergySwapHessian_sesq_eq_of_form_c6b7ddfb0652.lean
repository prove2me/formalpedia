-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartEnergySwapHessian_sesq_eq_of_form_c6b7ddfb0652
-- name    : P2M_GroundTheory_Heights__Heights_ChartEnergySwapHessian_sesq_eq_of_form_c6b7ddfb0652
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T00:18:20.401192+00:00
-- url     : https://prove2.me/theorems/ec2968ed-17aa-45fb-b00d-4c28bca573fb
-- title:
--   P2 M Ground Theory Heights  Heights Chart Energy Swap Hessian sesq eq of form c6b7ddfb0652: P2 M Ground Theory Heights  Heights Chart Energy Swap Hessian sesq eq of form c6b7ddfb0652
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Energy Swap Hessian sesq eq of form c6b7ddfb0652 construction uses the P2 M Ground Theory Heights  Heights Chart Energy Swap Hessian sesq eq of form c6b7ddfb0652 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/ChartHessHolo.lean#L91-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/ChartHessHolo.lean#L91-L100

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

theorem P2M_GroundTheory_Heights__Heights_ChartEnergySwapHessian_sesq_eq_of_form_c6b7ddfb0652 (H H₀ : (Fin D → ℂ) →L[ℝ] (Fin D → ℂ) →L[ℝ] ℝ)
    (L : (Fin D → ℂ) →L[ℂ] (Fin D → ℂ)) (R : (Fin D → ℂ) → (Fin D → ℂ) → ℝ)
    (hH : ∀ u v, H u v = H₀ (L u) (L v) + R u v)
    (hR₁ : ∀ u v, R (Complex.I • u) (Complex.I • v) = -R u v)
    (hR₂ : ∀ u v, R u (Complex.I • v) = R (Complex.I • u) v) (a b : Fin D → ℂ) :
    sesq H a b = sesq H₀ (L a) (L b) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartEnergySwapHessian».«sesq_eq_of_form» := P2M_GroundTheory_Heights__Heights_ChartEnergySwapHessian_sesq_eq_of_form_c6b7ddfb0652
