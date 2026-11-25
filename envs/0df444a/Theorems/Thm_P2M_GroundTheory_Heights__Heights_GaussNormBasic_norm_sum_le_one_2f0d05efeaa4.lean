-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_GaussNormBasic_norm_sum_le_one_2f0d05efeaa4
-- name    : P2M_GroundTheory_Heights__Heights_GaussNormBasic_norm_sum_le_one_2f0d05efeaa4
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:25:08.051801+00:00
-- url     : https://prove2.me/theorems/9a71b591-6b37-42fd-8d23-50b64d0013e4
-- title:
--   P2 M Ground Theory Heights  Heights Gauss Norm Basic norm sum le one 2f0d05efeaa4: P2 M Ground Theory Heights  Heights Gauss Norm Basic norm sum le one 2f0d05efeaa4
-- statement:
--   The P2 M Ground Theory Heights  Heights Gauss Norm Basic norm sum le one 2f0d05efeaa4 construction uses the P2 M Ground Theory Heights  Heights Gauss Norm Basic norm sum le one 2f0d05efeaa4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PGaussNormBasic.lean#L127-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PGaussNormBasic.lean#L127-L131

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_IsProbabilityMeasureSphereLaw
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PGaussNormBasic
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
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.GaussNormBasic
variable {L : Type*} [NormedField L] [IsUltrametricDist L]

theorem P2M_GroundTheory_Heights__Heights_GaussNormBasic_norm_sum_le_one_2f0d05efeaa4 {β : Type*} (s : Finset β) (f : β → L) (h : ∀ b ∈ s, ‖f b‖ ≤ 1) :
    ‖∑ b ∈ s, f b‖ ≤ 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«GaussNormBasic».«norm_sum_le_one» := P2M_GroundTheory_Heights__Heights_GaussNormBasic_norm_sum_le_one_2f0d05efeaa4
