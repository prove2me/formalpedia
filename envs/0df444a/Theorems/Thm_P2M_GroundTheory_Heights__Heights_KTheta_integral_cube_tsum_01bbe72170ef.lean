-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_KTheta_integral_cube_tsum_01bbe72170ef
-- name    : P2M_GroundTheory_Heights__Heights_KTheta_integral_cube_tsum_01bbe72170ef
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:26:29.871429+00:00
-- url     : https://prove2.me/theorems/cbb24b7c-6a00-4272-8a8e-85af12cae78f
-- title:
--   P2 M Ground Theory Heights  Heights KTheta integral cube tsum 01bbe72170ef: P2 M Ground Theory Heights  Heights KTheta integral cube tsum 01bbe72170ef
-- statement:
--   The P2 M Ground Theory Heights  Heights KTheta integral cube tsum 01bbe72170ef construction uses the P2 M Ground Theory Heights  Heights KTheta integral cube tsum 01bbe72170ef property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/ThetaGauss.lean#L114-L145
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/ThetaGauss.lean#L114-L145

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KernelsMatrix
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_NormInvSmulMemSphere
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ThetaGauss
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open Matrix MeasureTheory Real
open scoped MatrixOrder
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.KTheta
noncomputable section
variable {g : ℕ}

theorem P2M_GroundTheory_Heights__Heights_KTheta_integral_cube_tsum_01bbe72170ef (F : (Fin g → ℝ) → ℝ) (hF0 : ∀ x, 0 ≤ F x) (hFc : Continuous F)
    (hs : ∀ u, Summable fun k : Fin g → ℤ => F (intVec k + u)) :
    ∫ u in Set.Icc (0 : Fin g → ℝ) 1, ∑' k : Fin g → ℤ, F (intVec k + u) = ∫ x, F x := by sorry

alias «GroundTheory».«Heights₂».«Heights».«KTheta».«integral_cube_tsum» := P2M_GroundTheory_Heights__Heights_KTheta_integral_cube_tsum_01bbe72170ef
