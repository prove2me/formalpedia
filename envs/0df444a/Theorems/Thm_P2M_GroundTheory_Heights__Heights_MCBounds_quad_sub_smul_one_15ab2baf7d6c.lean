-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCBounds_quad_sub_smul_one_15ab2baf7d6c
-- name    : P2M_GroundTheory_Heights__Heights_MCBounds_quad_sub_smul_one_15ab2baf7d6c
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:34:34.320129+00:00
-- url     : https://prove2.me/theorems/a814b338-f315-4701-8284-a76354966a9a
-- title:
--   P2 M Ground Theory Heights  Heights MCBounds quad sub smul one 15ab2baf7d6c: P2 M Ground Theory Heights  Heights MCBounds quad sub smul one 15ab2baf7d6c
-- statement:
--   The P2 M Ground Theory Heights  Heights MCBounds quad sub smul one 15ab2baf7d6c construction uses the P2 M Ground Theory Heights  Heights MCBounds quad sub smul one 15ab2baf7d6c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/BoundsY.lean#L53-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/BoundsY.lean#L53-L55

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

theorem P2M_GroundTheory_Heights__Heights_MCBounds_quad_sub_smul_one_15ab2baf7d6c {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ) (l : ℝ)
    (x : ι → ℝ) : x ⬝ᵥ ((A - l • (1 : Matrix ι ι ℝ)) *ᵥ x) = x ⬝ᵥ (A *ᵥ x) - l * (x ⬝ᵥ x) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«MCBounds».«quad_sub_smul_one» := P2M_GroundTheory_Heights__Heights_MCBounds_quad_sub_smul_one_15ab2baf7d6c
