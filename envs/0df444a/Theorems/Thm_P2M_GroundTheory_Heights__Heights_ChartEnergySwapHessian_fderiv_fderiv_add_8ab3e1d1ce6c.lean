-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartEnergySwapHessian_fderiv_fderiv_add_8ab3e1d1ce6c
-- name    : P2M_GroundTheory_Heights__Heights_ChartEnergySwapHessian_fderiv_fderiv_add_8ab3e1d1ce6c
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T00:18:41.949205+00:00
-- url     : https://prove2.me/theorems/f993ddff-b6b1-49d7-bcf0-d63c75244231
-- title:
--   P2 M Ground Theory Heights  Heights Chart Energy Swap Hessian fderiv fderiv add 8ab3e1d1ce6c: P2 M Ground Theory Heights  Heights Chart Energy Swap Hessian fderiv fderiv add 8ab3e1d1ce6c
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Energy Swap Hessian fderiv fderiv add 8ab3e1d1ce6c construction uses the P2 M Ground Theory Heights  Heights Chart Energy Swap Hessian fderiv fderiv add 8ab3e1d1ce6c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/ChartHessHolo.lean#L79-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/ChartHessHolo.lean#L79-L89

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

theorem P2M_GroundTheory_Heights__Heights_ChartEnergySwapHessian_fderiv_fderiv_add_8ab3e1d1ce6c {f₁ f₂ : (Fin D → ℂ) → ℝ} {y : Fin D → ℂ} (h₁ : ContDiffAt ℝ 2 f₁ y)
    (h₂ : ContDiffAt ℝ 2 f₂ y) :
    fderiv ℝ (fderiv ℝ fun y' => f₁ y' + f₂ y') y = fderiv ℝ (fderiv ℝ f₁) y + fderiv ℝ (fderiv ℝ f₂) y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartEnergySwapHessian».«fderiv_fderiv_add» := P2M_GroundTheory_Heights__Heights_ChartEnergySwapHessian_fderiv_fderiv_add_8ab3e1d1ce6c
