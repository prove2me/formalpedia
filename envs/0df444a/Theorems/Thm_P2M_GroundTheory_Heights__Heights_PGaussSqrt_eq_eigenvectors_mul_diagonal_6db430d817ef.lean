-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PGaussSqrt_eq_eigenvectors_mul_diagonal_6db430d817ef
-- name    : P2M_GroundTheory_Heights__Heights_PGaussSqrt_eq_eigenvectors_mul_diagonal_6db430d817ef
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T04:13:33.400742+00:00
-- url     : https://prove2.me/theorems/4de72c9d-3bcd-47f4-b2fb-6496376ce1bf
-- title:
--   P2 M Ground Theory Heights  Heights PGauss Sqrt eq eigenvectors mul diagonal 6db430d817ef: P2 M Ground Theory Heights  Heights PGauss Sqrt eq eigenvectors mul diagonal 6db430d817ef
-- statement:
--   The P2 M Ground Theory Heights  Heights PGauss Sqrt eq eigenvectors mul diagonal 6db430d817ef construction uses the P2 M Ground Theory Heights  Heights PGauss Sqrt eq eigenvectors mul diagonal 6db430d817ef property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PGaussSqrt.lean#L11-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PGaussSqrt.lean#L11-L16

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGauss
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PGaussSqrt
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
open Matrix
open GroundTheory.Heights₂.Heights.PGaussSqrt

theorem P2M_GroundTheory_Heights__Heights_PGaussSqrt_eq_eigenvectors_mul_diagonal_6db430d817ef {g : ℕ} {Y : Matrix (Fin g) (Fin g) ℝ} (hH : Y.IsHermitian) :
    Y = (hH.eigenvectorUnitary : Matrix (Fin g) (Fin g) ℝ) * diagonal hH.eigenvalues *
      (hH.eigenvectorUnitary : Matrix (Fin g) (Fin g) ℝ)ᵀ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PGaussSqrt».«eq_eigenvectors_mul_diagonal» := P2M_GroundTheory_Heights__Heights_PGaussSqrt_eq_eigenvectors_mul_diagonal_6db430d817ef
