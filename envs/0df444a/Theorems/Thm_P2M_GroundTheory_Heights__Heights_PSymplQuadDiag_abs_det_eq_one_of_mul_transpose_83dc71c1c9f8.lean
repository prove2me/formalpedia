-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PSymplQuadDiag_abs_det_eq_one_of_mul_transpose_83dc71c1c9f8
-- name    : P2M_GroundTheory_Heights__Heights_PSymplQuadDiag_abs_det_eq_one_of_mul_transpose_83dc71c1c9f8
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T04:14:09.333413+00:00
-- url     : https://prove2.me/theorems/b9eb5a80-db7a-4dfe-baf4-0b0dec223c85
-- title:
--   P2 M Ground Theory Heights  Heights PSympl Quad Diag abs det eq one of mul transpose 83dc71c1c9f8: P2 M Ground Theory Heights  Heights PSympl Quad Diag abs det eq one of mul transpose 83dc71c1c9f8
-- statement:
--   The P2 M Ground Theory Heights  Heights PSympl Quad Diag abs det eq one of mul transpose 83dc71c1c9f8 construction uses the P2 M Ground Theory Heights  Heights PSympl Quad Diag abs det eq one of mul transpose 83dc71c1c9f8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PSymplQuadDiag.lean#L13-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PSymplQuadDiag.lean#L13-L19

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsSympl
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PSymplQuadDiag
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
noncomputable section
open GroundTheory.Heights₂.Heights.PSymplQuadDiag

theorem P2M_GroundTheory_Heights__Heights_PSymplQuadDiag_abs_det_eq_one_of_mul_transpose_83dc71c1c9f8 {ι : Type} [Fintype ι] [DecidableEq ι]
    (O : Matrix ι ι ℝ) (h : Oᵀ * O = 1) : |O.det| = 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PSymplQuadDiag».«abs_det_eq_one_of_mul_transpose» := P2M_GroundTheory_Heights__Heights_PSymplQuadDiag_abs_det_eq_one_of_mul_transpose_83dc71c1c9f8
