-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartEnergySwapHessian_det_fderiv_real_492d99151882
-- name    : P2M_GroundTheory_Heights__Heights_ChartEnergySwapHessian_det_fderiv_real_492d99151882
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T00:18:21.752884+00:00
-- url     : https://prove2.me/theorems/465faf3a-ef1f-44b0-9979-ccf28706913c
-- title:
--   P2 M Ground Theory Heights  Heights Chart Energy Swap Hessian det fderiv real 492d99151882: P2 M Ground Theory Heights  Heights Chart Energy Swap Hessian det fderiv real 492d99151882
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Energy Swap Hessian det fderiv real 492d99151882 construction uses the P2 M Ground Theory Heights  Heights Chart Energy Swap Hessian det fderiv real 492d99151882 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/ChartHessHolo.lean#L175-L182
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/ChartHessHolo.lean#L175-L182

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

theorem P2M_GroundTheory_Heights__Heights_ChartEnergySwapHessian_det_fderiv_real_492d99151882 {F : (Fin D → ℂ) → (Fin D → ℂ)} {y : Fin D → ℂ} (hF : DifferentiableAt ℂ F y) :
    (fderiv ℝ F y).det =
      Complex.normSq (LinearMap.toMatrix' (fderiv ℂ F y : (Fin D → ℂ) →ₗ[ℂ] (Fin D → ℂ))).det := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartEnergySwapHessian».«det_fderiv_real» := P2M_GroundTheory_Heights__Heights_ChartEnergySwapHessian_det_fderiv_real_492d99151882
