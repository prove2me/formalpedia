-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCBounds_abs_quad_le_949e60e6298d
-- name    : P2M_GroundTheory_Heights__Heights_MCBounds_abs_quad_le_949e60e6298d
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:28:50.439827+00:00
-- url     : https://prove2.me/theorems/63d2fb3e-d37f-4a0b-910d-42ba52b99cb9
-- title:
--   P2 M Ground Theory Heights  Heights MCBounds abs quad le 949e60e6298d: P2 M Ground Theory Heights  Heights MCBounds abs quad le 949e60e6298d
-- statement:
--   The P2 M Ground Theory Heights  Heights MCBounds abs quad le 949e60e6298d construction uses the P2 M Ground Theory Heights  Heights MCBounds abs quad le 949e60e6298d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/BoundsY.lean#L29-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/BoundsY.lean#L29-L40

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

theorem P2M_GroundTheory_Heights__Heights_MCBounds_abs_quad_le_949e60e6298d {ι : Type*} [Fintype ι] (A : Matrix ι ι ℝ) (x : ι → ℝ) :
    |x ⬝ᵥ (A *ᵥ x)| ≤ entrySum A * (x ⬝ᵥ x) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«MCBounds».«abs_quad_le» := P2M_GroundTheory_Heights__Heights_MCBounds_abs_quad_le_949e60e6298d
