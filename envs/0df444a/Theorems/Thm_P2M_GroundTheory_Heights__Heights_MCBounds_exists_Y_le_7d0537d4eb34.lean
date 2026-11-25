-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCBounds_exists_Y_le_7d0537d4eb34
-- name    : P2M_GroundTheory_Heights__Heights_MCBounds_exists_Y_le_7d0537d4eb34
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:28:42.335655+00:00
-- url     : https://prove2.me/theorems/bd69fa66-fd19-4745-bb15-4e86a821aeb5
-- title:
--   P2 M Ground Theory Heights  Heights MCBounds exists Y le 7d0537d4eb34: P2 M Ground Theory Heights  Heights MCBounds exists Y le 7d0537d4eb34
-- statement:
--   The P2 M Ground Theory Heights  Heights MCBounds exists Y le 7d0537d4eb34 construction uses the P2 M Ground Theory Heights  Heights MCBounds exists Y le 7d0537d4eb34 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/Bounds.lean#L114-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/Bounds.lean#L114-L126

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

theorem P2M_GroundTheory_Heights__Heights_MCBounds_exists_Y_le_7d0537d4eb34 : ∃ C : ℝ, 0 < C ∧ ∀ p ∈ D.K,
    ((C * D.radius p.1) • (1 : Matrix (Fin D.g) (Fin D.g) ℝ) - D.Y p.1).PosSemidef := by sorry

alias «GroundTheory».«Heights₂».«Heights».«MCBounds».«exists_Y_le» := P2M_GroundTheory_Heights__Heights_MCBounds_exists_Y_le_7d0537d4eb34
