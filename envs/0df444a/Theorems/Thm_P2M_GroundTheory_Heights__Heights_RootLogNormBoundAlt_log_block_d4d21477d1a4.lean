-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RootLogNormBoundAlt_log_block_d4d21477d1a4
-- name    : P2M_GroundTheory_Heights__Heights_RootLogNormBoundAlt_log_block_d4d21477d1a4
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:36:27.119632+00:00
-- url     : https://prove2.me/theorems/35a507f2-6b1a-5b37-8a4b-2d990b0c3129
-- title:
--   P2 M Ground Theory Heights  Heights Root Log Norm Bound Alt log block d4d21477d1a4: P2 M Ground Theory Heights  Heights Root Log Norm Bound Alt log block d4d21477d1a4
-- statement:
--   The P2 M Ground Theory Heights  Heights Root Log Norm Bound Alt log block d4d21477d1a4 construction uses the P2 M Ground Theory Heights  Heights Root Log Norm Bound Alt log block d4d21477d1a4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PRootLogNormBound.lean#L26-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PRootLogNormBound.lean#L26-L36

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

theorem P2M_GroundTheory_Heights__Heights_RootLogNormBoundAlt_log_block_d4d21477d1a4 (h₃ : PlueckerKernel.Statement) (j m : ℕ) (Z : Matrix (Fin j) (Fin m) ℂ)
    (hZ : ∀ a b, ‖Z a b‖ = 1) (a : ℂ) (ha : a ≠ 0) (v : PlIdx j m → ℂ)
    (hv : ∀ I, v I = a * (colsOf (onePipe Z) I).det) (hv0 : 0 < ‖WithLp.toLp 2 v‖) :
    -((j : ℝ) / 2 * Real.log (1 + m)) ≤ Real.log (‖a‖ / ‖WithLp.toLp 2 v‖) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RootLogNormBoundAlt».«log_block» := P2M_GroundTheory_Heights__Heights_RootLogNormBoundAlt_log_block_d4d21477d1a4
