-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCBounds_abs_mul_le_dot_107bf1204f91
-- name    : P2M_GroundTheory_Heights__Heights_MCBounds_abs_mul_le_dot_107bf1204f91
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:28:52.110502+00:00
-- url     : https://prove2.me/theorems/58b6537c-c920-40d3-ae83-a4e73251e4da
-- title:
--   P2 M Ground Theory Heights  Heights MCBounds abs mul le dot 107bf1204f91: P2 M Ground Theory Heights  Heights MCBounds abs mul le dot 107bf1204f91
-- statement:
--   The P2 M Ground Theory Heights  Heights MCBounds abs mul le dot 107bf1204f91 construction uses the P2 M Ground Theory Heights  Heights MCBounds abs mul le dot 107bf1204f91 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/BoundsY.lean#L23-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/BoundsY.lean#L23-L27

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_BoundsY
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.MCBounds
open Matrix
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_MCBounds_abs_mul_le_dot_107bf1204f91 {ι : Type*} [Fintype ι] (x : ι → ℝ) (j k : ι) :
    |x j| * |x k| ≤ x ⬝ᵥ x := by sorry

alias «GroundTheory».«Heights₂».«Heights».«MCBounds».«abs_mul_le_dot» := P2M_GroundTheory_Heights__Heights_MCBounds_abs_mul_le_dot_107bf1204f91
