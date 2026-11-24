-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCCusp_dot_mulVec_symm_9b8f1a0cd591
-- name    : P2M_GroundTheory_Heights__Heights_MCCusp_dot_mulVec_symm_9b8f1a0cd591
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:35:34.033318+00:00
-- url     : https://prove2.me/theorems/9e605d21-c825-469a-8b46-a9b60b62f63d
-- title:
--   P2 M Ground Theory Heights  Heights MCCusp dot mul Vec symm 9b8f1a0cd591: P2 M Ground Theory Heights  Heights MCCusp dot mul Vec symm 9b8f1a0cd591
-- statement:
--   The P2 M Ground Theory Heights  Heights MCCusp dot mul Vec symm 9b8f1a0cd591 construction uses the P2 M Ground Theory Heights  Heights MCCusp dot mul Vec symm 9b8f1a0cd591 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/TransposeEqOfPosSemidef.lean#L15-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/TransposeEqOfPosSemidef.lean#L15-L17

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_HermValueIsLeast
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_TransposeEqOfPosSemidef
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.MCCusp
open Matrix GroundTheory.Heights₂.Heights.MCSchur
noncomputable section
variable {ι : Type*} [Fintype ι]

theorem P2M_GroundTheory_Heights__Heights_MCCusp_dot_mulVec_symm_9b8f1a0cd591 {Z : Matrix ι ι ℝ} (hZ : Zᵀ = Z) (u w : ι → ℝ) :
    u ⬝ᵥ (Z *ᵥ w) = w ⬝ᵥ (Z *ᵥ u) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«MCCusp».«dot_mulVec_symm» := P2M_GroundTheory_Heights__Heights_MCCusp_dot_mulVec_symm_9b8f1a0cd591
