-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartMongeAmpereAffineInvariance_eq_sum_smul_single_a55bf1f87056
-- name    : P2M_GroundTheory_Heights__Heights_ChartMongeAmpereAffineInvariance_eq_sum_smul_single_a55bf1f87056
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:15:30.60587+00:00
-- url     : https://prove2.me/theorems/bfc6a537-7b82-4622-b03f-e54e9925a99d
-- title:
--   P2 M Ground Theory Heights  Heights Chart Monge Ampere Affine Invariance eq sum smul single a55bf1f87056: P2 M Ground Theory Heights  Heights Chart Monge Ampere Affine Invariance eq sum smul single a5
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Monge Ampere Affine Invariance eq sum smul single a55bf1f87056 construction uses the P2 M Ground Theory Heights  Heights Chart Monge Ampere Affine Invariance eq sum smul single a55bf1f87056 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/ChartMassAffine.lean#L83-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/ChartMassAffine.lean#L83-L85

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
variable (H : (Fin D → ℂ) →L[ℝ] (Fin D → ℂ) →L[ℝ] ℝ)

theorem P2M_GroundTheory_Heights__Heights_ChartMongeAmpereAffineInvariance_eq_sum_smul_single_a55bf1f87056 (a : Fin D → ℂ) : a = ∑ k, a k • (Pi.single k 1 : Fin D → ℂ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartMongeAmpereAffineInvariance».«eq_sum_smul_single» := P2M_GroundTheory_Heights__Heights_ChartMongeAmpereAffineInvariance_eq_sum_smul_single_a55bf1f87056
