-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_exists_pow_mul_sub_rename_mem_1157a3bef5d7
-- name    : P2M_GroundTheory_Heights__Heights_exists_pow_mul_sub_rename_mem_1157a3bef5d7
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T04:46:06.068312+00:00
-- url     : https://prove2.me/theorems/a91376c3-6e94-40c5-9e86-ae9dcb8c6186
-- title:
--   P2 M Ground Theory Heights  Heights exists pow mul sub rename mem 1157a3bef5d7: P2 M Ground Theory Heights  Heights exists pow mul sub rename mem 1157a3bef5d7
-- statement:
--   The P2 M Ground Theory Heights  Heights exists pow mul sub rename mem 1157a3bef5d7 construction uses the P2 M Ground Theory Heights  Heights exists pow mul sub rename mem 1157a3bef5d7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/RadicalAwayRabinowitsch.lean#L80-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/RadicalAwayRabinowitsch.lean#L80-L111

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGenericFibreRadicalAway
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_RadicalAwayRabinowitsch
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
variable {R : Type*} [CommRing R] {ι : Type*}

theorem P2M_GroundTheory_Heights__Heights_exists_pow_mul_sub_rename_mem_1157a3bef5d7 (g : MvPolynomial ι R) (h : MvPolynomial (Option ι) R) :
    ∃ (N : ℕ) (f : MvPolynomial ι R), rename some g ^ N * h - rename some f ∈
      (Ideal.span {X none * rename some g - 1} : Ideal (MvPolynomial (Option ι) R)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«exists_pow_mul_sub_rename_mem» := P2M_GroundTheory_Heights__Heights_exists_pow_mul_sub_rename_mem_1157a3bef5d7
