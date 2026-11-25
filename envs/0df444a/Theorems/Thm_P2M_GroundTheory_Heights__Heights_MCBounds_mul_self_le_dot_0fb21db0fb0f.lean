-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCBounds_mul_self_le_dot_0fb21db0fb0f
-- name    : P2M_GroundTheory_Heights__Heights_MCBounds_mul_self_le_dot_0fb21db0fb0f
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:28:47.603071+00:00
-- url     : https://prove2.me/theorems/402e169d-59eb-48af-aab9-7dffde17673c
-- title:
--   P2 M Ground Theory Heights  Heights MCBounds mul self le dot 0fb21db0fb0f: P2 M Ground Theory Heights  Heights MCBounds mul self le dot 0fb21db0fb0f
-- statement:
--   The P2 M Ground Theory Heights  Heights MCBounds mul self le dot 0fb21db0fb0f construction uses the P2 M Ground Theory Heights  Heights MCBounds mul self le dot 0fb21db0fb0f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/BoundsY.lean#L19-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/BoundsY.lean#L19-L21

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

theorem P2M_GroundTheory_Heights__Heights_MCBounds_mul_self_le_dot_0fb21db0fb0f {ι : Type*} [Fintype ι] (x : ι → ℝ) (j : ι) : x j * x j ≤ x ⬝ᵥ x := by sorry

alias «GroundTheory».«Heights₂».«Heights».«MCBounds».«mul_self_le_dot» := P2M_GroundTheory_Heights__Heights_MCBounds_mul_self_le_dot_0fb21db0fb0f
