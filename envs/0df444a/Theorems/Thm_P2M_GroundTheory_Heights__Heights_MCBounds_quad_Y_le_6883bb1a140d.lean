-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCBounds_quad_Y_le_6883bb1a140d
-- name    : P2M_GroundTheory_Heights__Heights_MCBounds_quad_Y_le_6883bb1a140d
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:28:52.513838+00:00
-- url     : https://prove2.me/theorems/42c14b90-5cc4-4c46-83dc-88f468fc438f
-- title:
--   P2 M Ground Theory Heights  Heights MCBounds quad Y le 6883bb1a140d: P2 M Ground Theory Heights  Heights MCBounds quad Y le 6883bb1a140d
-- statement:
--   The P2 M Ground Theory Heights  Heights MCBounds quad Y le 6883bb1a140d construction uses the P2 M Ground Theory Heights  Heights MCBounds quad Y le 6883bb1a140d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/Bounds.lean#L85-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/Bounds.lean#L85-L112

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_DetIneq
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_BoundsY
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Bounds
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
open scoped ComplexOrder
noncomputable section
variable (D : PeriodChartData)

theorem P2M_GroundTheory_Heights__Heights_MCBounds_quad_Y_le_6883bb1a140d {z : Fin D.n → ℂ} (hz : z ∈ D.U) (M : ℝ)
    (hM : entrySum ((D.τ0 z).map Complex.im) ≤ M) (x : Fin D.g → ℝ) :
    x ⬝ᵥ (D.Y z *ᵥ x) ≤ (M + ∑ j, entrySum (D.B j)) * D.radius z * (x ⬝ᵥ x) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«MCBounds».«quad_Y_le» := P2M_GroundTheory_Heights__Heights_MCBounds_quad_Y_le_6883bb1a140d
