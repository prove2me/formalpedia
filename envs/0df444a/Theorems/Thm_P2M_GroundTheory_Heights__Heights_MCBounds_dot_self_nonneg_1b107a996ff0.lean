-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCBounds_dot_self_nonneg_1b107a996ff0
-- name    : P2M_GroundTheory_Heights__Heights_MCBounds_dot_self_nonneg_1b107a996ff0
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:33:21.918084+00:00
-- url     : https://prove2.me/theorems/85d75b54-096e-448a-b40c-d6cde8d923b9
-- title:
--   P2 M Ground Theory Heights  Heights MCBounds dot self nonneg 1b107a996ff0: P2 M Ground Theory Heights  Heights MCBounds dot self nonneg 1b107a996ff0
-- statement:
--   The P2 M Ground Theory Heights  Heights MCBounds dot self nonneg 1b107a996ff0 construction uses the P2 M Ground Theory Heights  Heights MCBounds dot self nonneg 1b107a996ff0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/BoundsY.lean#L16-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/BoundsY.lean#L16-L17

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

theorem P2M_GroundTheory_Heights__Heights_MCBounds_dot_self_nonneg_1b107a996ff0 {ι : Type*} [Fintype ι] (v : ι → ℝ) : 0 ≤ v ⬝ᵥ v := by sorry

alias «GroundTheory».«Heights₂».«Heights».«MCBounds».«dot_self_nonneg» := P2M_GroundTheory_Heights__Heights_MCBounds_dot_self_nonneg_1b107a996ff0
