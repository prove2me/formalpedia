-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartMongeAmpereAffineInvariance_smul_eq_re_add_im_4c7b8f6c23de
-- name    : P2M_GroundTheory_Heights__Heights_ChartMongeAmpereAffineInvariance_smul_eq_re_add_im_4c7b8f6c23de
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:32:21.991989+00:00
-- url     : https://prove2.me/theorems/da386680-0c80-4da3-b13b-c1c5a5bc0f2d
-- title:
--   P2 M Ground Theory Heights  Heights Chart Monge Ampere Affine Invariance smul eq re add im 4c7b8f6c23de: P2 M Ground Theory Heights  Heights Chart Monge Ampere Affine Invariance smul eq re add im 4c7b
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Monge Ampere Affine Invariance smul eq re add im 4c7b8f6c23de construction uses the P2 M Ground Theory Heights  Heights Chart Monge Ampere Affine Invariance smul eq re add im 4c7b8f6c23de property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/ChartMassAffine.lean#L58-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/ChartMassAffine.lean#L58-L62

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

theorem P2M_GroundTheory_Heights__Heights_ChartMongeAmpereAffineInvariance_smul_eq_re_add_im_4c7b8f6c23de (a : ℂ) (u : Fin D → ℂ) : a • u = a.re • u + a.im • (Complex.I • u) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartMongeAmpereAffineInvariance».«smul_eq_re_add_im» := P2M_GroundTheory_Heights__Heights_ChartMongeAmpereAffineInvariance_smul_eq_re_add_im_4c7b8f6c23de
