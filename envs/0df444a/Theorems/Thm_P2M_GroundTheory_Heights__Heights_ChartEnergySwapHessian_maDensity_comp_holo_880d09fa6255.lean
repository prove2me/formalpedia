-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartEnergySwapHessian_maDensity_comp_holo_880d09fa6255
-- name    : P2M_GroundTheory_Heights__Heights_ChartEnergySwapHessian_maDensity_comp_holo_880d09fa6255
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T00:18:16.491314+00:00
-- url     : https://prove2.me/theorems/0e7003ac-3036-4921-bf3e-b4d1d199a14c
-- title:
--   P2 M Ground Theory Heights  Heights Chart Energy Swap Hessian ma Density comp holo 880d09fa6255: P2 M Ground Theory Heights  Heights Chart Energy Swap Hessian ma Density comp holo 880d09fa6255
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Energy Swap Hessian ma Density comp holo 880d09fa6255 construction uses the P2 M Ground Theory Heights  Heights Chart Energy Swap Hessian ma Density comp holo 880d09fa6255 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/ChartHessHolo.lean#L161-L173
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/ChartHessHolo.lean#L161-L173

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

theorem P2M_GroundTheory_Heights__Heights_ChartEnergySwapHessian_maDensity_comp_holo_880d09fa6255 (Φ' Φ : Fin D → (Fin D → ℂ) → ℝ) (F : (Fin D → ℂ) → (Fin D → ℂ))
    (h : (Fin D → ℂ) → ℂ) (y : Fin D → ℂ) (hΦ : ∀ j, ContDiffAt ℝ 2 (Φ j) (F y)) (hF : ContDiffAt ℂ 2 F y)
    (hh : ContDiffAt ℂ 2 h y) (hΦ' : ∀ j, Φ' j =ᶠ[𝓝 y] fun y' => Φ j (F y') + (h y').re) :
    maDensity Φ' y = Complex.normSq (LinearMap.toMatrix' (fderiv ℂ F y : (Fin D → ℂ) →ₗ[ℂ] (Fin D → ℂ))).det *
      maDensity Φ (F y) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartEnergySwapHessian».«maDensity_comp_holo» := P2M_GroundTheory_Heights__Heights_ChartEnergySwapHessian_maDensity_comp_holo_880d09fa6255
