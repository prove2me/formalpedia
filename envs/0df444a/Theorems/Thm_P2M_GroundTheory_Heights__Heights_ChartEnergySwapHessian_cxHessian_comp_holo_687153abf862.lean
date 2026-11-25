-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartEnergySwapHessian_cxHessian_comp_holo_687153abf862
-- name    : P2M_GroundTheory_Heights__Heights_ChartEnergySwapHessian_cxHessian_comp_holo_687153abf862
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T00:18:09.046034+00:00
-- url     : https://prove2.me/theorems/e5850eac-bb01-4cc7-86c1-f8fdad79c8c4
-- title:
--   P2 M Ground Theory Heights  Heights Chart Energy Swap Hessian cx Hessian comp holo 687153abf862: P2 M Ground Theory Heights  Heights Chart Energy Swap Hessian cx Hessian comp holo 687153abf862
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Energy Swap Hessian cx Hessian comp holo 687153abf862 construction uses the P2 M Ground Theory Heights  Heights Chart Energy Swap Hessian cx Hessian comp holo 687153abf862 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/ChartHessHolo.lean#L119-L159
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/ChartHessHolo.lean#L119-L159

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

theorem P2M_GroundTheory_Heights__Heights_ChartEnergySwapHessian_cxHessian_comp_holo_687153abf862 (f g : (Fin D → ℂ) → ℝ) (F : (Fin D → ℂ) → (Fin D → ℂ)) (h : (Fin D → ℂ) → ℂ)
    (y : Fin D → ℂ) (hg : ContDiffAt ℝ 2 g (F y)) (hF : ContDiffAt ℂ 2 F y) (hh : ContDiffAt ℂ 2 h y)
    (hf : f =ᶠ[𝓝 y] fun y' => g (F y') + (h y').re) :
    cxHessian f y = (LinearMap.toMatrix' (fderiv ℂ F y : (Fin D → ℂ) →ₗ[ℂ] (Fin D → ℂ)))ᵀ *
      cxHessian g (F y) * (LinearMap.toMatrix' (fderiv ℂ F y : (Fin D → ℂ) →ₗ[ℂ] (Fin D → ℂ))).map
        (starRingEnd ℂ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartEnergySwapHessian».«cxHessian_comp_holo» := P2M_GroundTheory_Heights__Heights_ChartEnergySwapHessian_cxHessian_comp_holo_687153abf862
