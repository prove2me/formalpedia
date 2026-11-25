-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PGaussDualMin_qf_inv_transpose_mulVec_dfe09d35d919
-- name    : P2M_GroundTheory_Heights__Heights_PGaussDualMin_qf_inv_transpose_mulVec_dfe09d35d919
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T04:13:47.378657+00:00
-- url     : https://prove2.me/theorems/f624d646-d98b-4d5e-b8eb-ef4f75ec134e
-- title:
--   P2 M Ground Theory Heights  Heights PGauss Dual Min qf inv transpose mul Vec dfe09d35d919: P2 M Ground Theory Heights  Heights PGauss Dual Min qf inv transpose mul Vec dfe09d35d919
-- statement:
--   The P2 M Ground Theory Heights  Heights PGauss Dual Min qf inv transpose mul Vec dfe09d35d919 construction uses the P2 M Ground Theory Heights  Heights PGauss Dual Min qf inv transpose mul Vec dfe09d35d919 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PGaussDualMin.lean#L15-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PGaussDualMin.lean#L15-L24

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGauss
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PGaussDualMin
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
open GroundTheory.Heights₂.Heights.PGaussDualMin

theorem P2M_GroundTheory_Heights__Heights_PGaussDualMin_qf_inv_transpose_mulVec_dfe09d35d919 {g : ℕ} (B : Matrix (Fin g) (Fin g) ℝ) (hB : B.det ≠ 0)
    (m : Fin g → ℝ) : qf (Bᵀ * B)⁻¹ (Bᵀ *ᵥ m) = m ⬝ᵥ m := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PGaussDualMin».«qf_inv_transpose_mulVec» := P2M_GroundTheory_Heights__Heights_PGaussDualMin_qf_inv_transpose_mulVec_dfe09d35d919
