-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCBounds_quad_smul_one_sub_79ae7301e3b8
-- name    : P2M_GroundTheory_Heights__Heights_MCBounds_quad_smul_one_sub_79ae7301e3b8
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:34:06.922278+00:00
-- url     : https://prove2.me/theorems/21248145-5593-4ef6-84a8-4b21686d1076
-- title:
--   P2 M Ground Theory Heights  Heights MCBounds quad smul one sub 79ae7301e3b8: P2 M Ground Theory Heights  Heights MCBounds quad smul one sub 79ae7301e3b8
-- statement:
--   The P2 M Ground Theory Heights  Heights MCBounds quad smul one sub 79ae7301e3b8 construction uses the P2 M Ground Theory Heights  Heights MCBounds quad smul one sub 79ae7301e3b8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/BoundsY.lean#L49-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/BoundsY.lean#L49-L51

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

theorem P2M_GroundTheory_Heights__Heights_MCBounds_quad_smul_one_sub_79ae7301e3b8 {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ) (l : ℝ)
    (x : ι → ℝ) : x ⬝ᵥ ((l • (1 : Matrix ι ι ℝ) - A) *ᵥ x) = l * (x ⬝ᵥ x) - x ⬝ᵥ (A *ᵥ x) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«MCBounds».«quad_smul_one_sub» := P2M_GroundTheory_Heights__Heights_MCBounds_quad_smul_one_sub_79ae7301e3b8
