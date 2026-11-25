-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_blockSum_nonneg_b0b5b7ed1f1e
-- name    : P2M_GroundTheory_Heights__Heights_blockSum_nonneg_b0b5b7ed1f1e
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:44:31.795585+00:00
-- url     : https://prove2.me/theorems/a3719336-3f74-494d-9437-e806d869138f
-- title:
--   P2 M Ground Theory Heights  Heights block Sum nonneg b0b5b7ed1f1e: P2 M Ground Theory Heights  Heights block Sum nonneg b0b5b7ed1f1e
-- statement:
--   The P2 M Ground Theory Heights  Heights block Sum nonneg b0b5b7ed1f1e construction uses the P2 M Ground Theory Heights  Heights block Sum nonneg b0b5b7ed1f1e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/Comparison.lean#L151-L179
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/Comparison.lean#L151-L179

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_FiniteSupportHeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Comparison
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
open MvPolynomial NumberField
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
variable {K : Type*} [Field K] [NumberField K]
omit [Fintype ι] [DecidableEq ι]

theorem P2M_GroundTheory_Heights__Heights_blockSum_nonneg_b0b5b7ed1f1e (y : Cone n K) (k : ι) (hy : y k ≠ 0) : 0 ≤ blockSum y k := by sorry

alias «GroundTheory».«Heights₂».«Heights».«blockSum_nonneg» := P2M_GroundTheory_Heights__Heights_blockSum_nonneg_b0b5b7ed1f1e
