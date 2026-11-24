-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCBounds_quad_symm_4b25d90b3d61
-- name    : P2M_GroundTheory_Heights__Heights_MCBounds_quad_symm_4b25d90b3d61
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:35:25.877807+00:00
-- url     : https://prove2.me/theorems/ea8430ec-49c8-4c51-9512-4055c771f517
-- title:
--   P2 M Ground Theory Heights  Heights MCBounds quad symm 4b25d90b3d61: P2 M Ground Theory Heights  Heights MCBounds quad symm 4b25d90b3d61
-- statement:
--   The P2 M Ground Theory Heights  Heights MCBounds quad symm 4b25d90b3d61 construction uses the P2 M Ground Theory Heights  Heights MCBounds quad symm 4b25d90b3d61 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/BoundsY.lean#L69-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/BoundsY.lean#L69-L71

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

theorem P2M_GroundTheory_Heights__Heights_MCBounds_quad_symm_4b25d90b3d61 {ι : Type*} [Fintype ι] {A : Matrix ι ι ℝ} (hs : Aᵀ = A) (u v : ι → ℝ) :
    v ⬝ᵥ (A *ᵥ u) = u ⬝ᵥ (A *ᵥ v) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«MCBounds».«quad_symm» := P2M_GroundTheory_Heights__Heights_MCBounds_quad_symm_4b25d90b3d61
