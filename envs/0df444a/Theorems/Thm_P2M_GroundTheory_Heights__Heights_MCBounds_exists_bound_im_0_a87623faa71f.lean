-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCBounds_exists_bound_im_0_a87623faa71f
-- name    : P2M_GroundTheory_Heights__Heights_MCBounds_exists_bound_im_0_a87623faa71f
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:30:50.393053+00:00
-- url     : https://prove2.me/theorems/f8094fb4-d7d6-4e8b-874a-3295b6d65c61
-- title:
--   P2 M Ground Theory Heights  Heights MCBounds exists bound im 0 a87623faa71f: P2 M Ground Theory Heights  Heights MCBounds exists bound im 0 a87623faa71f
-- statement:
--   The P2 M Ground Theory Heights  Heights MCBounds exists bound im 0 a87623faa71f construction uses the P2 M Ground Theory Heights  Heights MCBounds exists bound im 0 a87623faa71f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/Bounds.lean#L67-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/Bounds.lean#L67-L83

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

theorem P2M_GroundTheory_Heights__Heights_MCBounds_exists_bound_im_0_a87623faa71f : ∃ M : ℝ, 0 ≤ M ∧
    ∀ p ∈ D.K, entrySum ((D.τ0 p.1).map Complex.im) ≤ M := by sorry

alias «GroundTheory».«Heights₂».«Heights».«MCBounds».«exists_bound_imτ0» := P2M_GroundTheory_Heights__Heights_MCBounds_exists_bound_im_0_a87623faa71f
