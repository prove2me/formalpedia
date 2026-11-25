-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RootLogNormBoundAlt_norm_block_le_93e0782b40a7
-- name    : P2M_GroundTheory_Heights__Heights_RootLogNormBoundAlt_norm_block_le_93e0782b40a7
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:36:46.487445+00:00
-- url     : https://prove2.me/theorems/6cf2a901-559f-4f06-aa89-9d4fb83cf94d
-- title:
--   P2 M Ground Theory Heights  Heights Root Log Norm Bound Alt norm block le 93e0782b40a7: P2 M Ground Theory Heights  Heights Root Log Norm Bound Alt norm block le 93e0782b40a7
-- statement:
--   The P2 M Ground Theory Heights  Heights Root Log Norm Bound Alt norm block le 93e0782b40a7 construction uses the P2 M Ground Theory Heights  Heights Root Log Norm Bound Alt norm block le 93e0782b40a7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PRootLogNormBound.lean#L13-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PRootLogNormBound.lean#L13-L24

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrassHeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PRootLogNormBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial Matrix
noncomputable section
open GroundTheory.Heights₂.Heights.RootLogNormBoundAlt

theorem P2M_GroundTheory_Heights__Heights_RootLogNormBoundAlt_norm_block_le_93e0782b40a7 (h₃ : PlueckerKernel.Statement) (j m : ℕ) (Z : Matrix (Fin j) (Fin m) ℂ)
    (hZ : ∀ a b, ‖Z a b‖ = 1) (a : ℂ) (v : PlIdx j m → ℂ)
    (hv : ∀ I, v I = a * (colsOf (onePipe Z) I).det) :
    ‖WithLp.toLp 2 v‖ ≤ ‖a‖ * Real.sqrt ((1 + m : ℝ) ^ j) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RootLogNormBoundAlt».«norm_block_le» := P2M_GroundTheory_Heights__Heights_RootLogNormBoundAlt_norm_block_le_93e0782b40a7
