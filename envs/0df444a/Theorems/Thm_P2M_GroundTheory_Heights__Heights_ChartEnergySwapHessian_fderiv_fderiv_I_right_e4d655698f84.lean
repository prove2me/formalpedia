-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartEnergySwapHessian_fderiv_fderiv_I_right_e4d655698f84
-- name    : P2M_GroundTheory_Heights__Heights_ChartEnergySwapHessian_fderiv_fderiv_I_right_e4d655698f84
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:07:14.545822+00:00
-- url     : https://prove2.me/theorems/e501729e-d2a5-456c-832d-9363c33b86d8
-- title:
--   P2 M Ground Theory Heights  Heights Chart Energy Swap Hessian fderiv fderiv I right e4d655698f84: P2 M Ground Theory Heights  Heights Chart Energy Swap Hessian fderiv fderiv I right e4d655698f84
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Energy Swap Hessian fderiv fderiv I right e4d655698f84 construction uses the P2 M Ground Theory Heights  Heights Chart Energy Swap Hessian fderiv fderiv I right e4d655698f84 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/ChartHessHolo.lean#L24-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/ChartHessHolo.lean#L24-L39

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

theorem P2M_GroundTheory_Heights__Heights_ChartEnergySwapHessian_fderiv_fderiv_I_right_e4d655698f84 {F : (Fin D → ℂ) → E'} {y : Fin D → ℂ} (hF : ContDiffAt ℂ 2 F y)
    (u v : Fin D → ℂ) :
    fderiv ℝ (fderiv ℝ F) y u (Complex.I • v) = Complex.I • fderiv ℝ (fderiv ℝ F) y u v := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartEnergySwapHessian».«fderiv_fderiv_I_right» := P2M_GroundTheory_Heights__Heights_ChartEnergySwapHessian_fderiv_fderiv_I_right_e4d655698f84
