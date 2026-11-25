-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartEnergySwapHessian_fderiv_fderiv_I_left_81bab7189de8
-- name    : P2M_GroundTheory_Heights__Heights_ChartEnergySwapHessian_fderiv_fderiv_I_left_81bab7189de8
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T00:18:27.109562+00:00
-- url     : https://prove2.me/theorems/e29bac31-930c-488e-bbf0-eb1729e943f1
-- title:
--   P2 M Ground Theory Heights  Heights Chart Energy Swap Hessian fderiv fderiv I left 81bab7189de8: P2 M Ground Theory Heights  Heights Chart Energy Swap Hessian fderiv fderiv I left 81bab7189de8
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Energy Swap Hessian fderiv fderiv I left 81bab7189de8 construction uses the P2 M Ground Theory Heights  Heights Chart Energy Swap Hessian fderiv fderiv I left 81bab7189de8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/ChartHessHolo.lean#L47-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/ChartHessHolo.lean#L47-L51

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

theorem P2M_GroundTheory_Heights__Heights_ChartEnergySwapHessian_fderiv_fderiv_I_left_81bab7189de8 {F : (Fin D → ℂ) → E'} {y : Fin D → ℂ} (hF : ContDiffAt ℂ 2 F y)
    (u v : Fin D → ℂ) :
    fderiv ℝ (fderiv ℝ F) y (Complex.I • u) v = Complex.I • fderiv ℝ (fderiv ℝ F) y u v := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartEnergySwapHessian».«fderiv_fderiv_I_left» := P2M_GroundTheory_Heights__Heights_ChartEnergySwapHessian_fderiv_fderiv_I_left_81bab7189de8
