-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCSchur_inv_toBlocks___eq_c87d050c0061
-- name    : P2M_GroundTheory_Heights__Heights_MCSchur_inv_toBlocks___eq_c87d050c0061
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:47:50.443802+00:00
-- url     : https://prove2.me/theorems/e4ce479b-4144-5208-997d-14d03b3ac531
-- title:
--   P2 M Ground Theory Heights  Heights MCSchur inv to Blocks   eq c87d050c0061: P2 M Ground Theory Heights  Heights MCSchur inv to Blocks   eq c87d050c0061
-- statement:
--   The P2 M Ground Theory Heights  Heights MCSchur inv to Blocks   eq c87d050c0061 construction uses the P2 M Ground Theory Heights  Heights MCSchur inv to Blocks   eq c87d050c0061 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/HermValueIsLeast.lean#L24-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/HermValueIsLeast.lean#L24-L41

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_HermValueIsLeast
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.MCSchur
open Matrix
noncomputable section
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

theorem P2M_GroundTheory_Heights__Heights_MCSchur_inv_toBlocks___eq_c87d050c0061 (Y : Matrix (m ⊕ n) (m ⊕ n) ℝ) (hY : IsUnit Y.det)
    (hA : IsUnit (Y⁻¹).toBlocks₁₁.det) :
    (Y.toBlocks₂₂)⁻¹ = (Y⁻¹).toBlocks₂₂ - (Y⁻¹).toBlocks₂₁ * ((Y⁻¹).toBlocks₁₁)⁻¹ * (Y⁻¹).toBlocks₁₂ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«MCSchur».«inv_toBlocks₂₂_eq» := P2M_GroundTheory_Heights__Heights_MCSchur_inv_toBlocks___eq_c87d050c0061
