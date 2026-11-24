-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCBounds_inv_le_of_ge_22d5970a02ea
-- name    : P2M_GroundTheory_Heights__Heights_MCBounds_inv_le_of_ge_22d5970a02ea
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:34:41.489641+00:00
-- url     : https://prove2.me/theorems/3a39d64f-8160-4fb7-acc7-244eb1141fa0
-- title:
--   P2 M Ground Theory Heights  Heights MCBounds inv le of ge 22d5970a02ea: P2 M Ground Theory Heights  Heights MCBounds inv le of ge 22d5970a02ea
-- statement:
--   The P2 M Ground Theory Heights  Heights MCBounds inv le of ge 22d5970a02ea construction uses the P2 M Ground Theory Heights  Heights MCBounds inv le of ge 22d5970a02ea property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/BoundsY.lean#L103-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/BoundsY.lean#L103-L124

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

theorem P2M_GroundTheory_Heights__Heights_MCBounds_inv_le_of_ge_22d5970a02ea {ι : Type*} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℝ} {c : ℝ}
    (hc : 0 < c) (h : (A - c • (1 : Matrix ι ι ℝ)).PosSemidef) :
    (c⁻¹ • (1 : Matrix ι ι ℝ) - A⁻¹).PosSemidef := by sorry

alias «GroundTheory».«Heights₂».«Heights».«MCBounds».«inv_le_of_ge» := P2M_GroundTheory_Heights__Heights_MCBounds_inv_le_of_ge_22d5970a02ea
