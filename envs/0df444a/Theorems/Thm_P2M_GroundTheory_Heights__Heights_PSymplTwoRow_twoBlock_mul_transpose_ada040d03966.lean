-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PSymplTwoRow_twoBlock_mul_transpose_ada040d03966
-- name    : P2M_GroundTheory_Heights__Heights_PSymplTwoRow_twoBlock_mul_transpose_ada040d03966
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T04:14:46.756174+00:00
-- url     : https://prove2.me/theorems/c72c8506-2e2e-4d75-962e-73d61de201b9
-- title:
--   P2 M Ground Theory Heights  Heights PSympl Two Row two Block mul transpose ada040d03966: P2 M Ground Theory Heights  Heights PSympl Two Row two Block mul transpose ada040d03966
-- statement:
--   The P2 M Ground Theory Heights  Heights PSympl Two Row two Block mul transpose ada040d03966 construction uses the P2 M Ground Theory Heights  Heights PSympl Two Row two Block mul transpose ada040d03966 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PSymplTwoRow.lean#L15-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PSymplTwoRow.lean#L15-L22

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsSympl
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PSymplTwoRow
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
open GroundTheory.Heights₂.Heights.PSymplTwoRow

theorem P2M_GroundTheory_Heights__Heights_PSymplTwoRow_twoBlock_mul_transpose_ada040d03966 {n : ℕ} {c d x y : ℤ} (h : x * c + y * d = 1) :
    twoBlock n c d x y * (twoBlock n x y c d)ᵀ = 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PSymplTwoRow».«twoBlock_mul_transpose» := P2M_GroundTheory_Heights__Heights_PSymplTwoRow_twoBlock_mul_transpose_ada040d03966
