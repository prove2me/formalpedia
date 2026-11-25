-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LocalSectionLengthSum_length_quot_smul_top_eq_c98b42d6d7fe
-- name    : P2M_GroundTheory_Heights__Heights_LocalSectionLengthSum_length_quot_smul_top_eq_c98b42d6d7fe
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:27:55.458673+00:00
-- url     : https://prove2.me/theorems/f3e9f7e0-9be8-43ee-9d90-85fd8420580a
-- title:
--   P2 M Ground Theory Heights  Heights Local Section Length Sum length quot smul top eq c98b42d6d7fe: P2 M Ground Theory Heights  Heights Local Section Length Sum length quot smul top eq c98b42d6d7fe
-- statement:
--   The P2 M Ground Theory Heights  Heights Local Section Length Sum length quot smul top eq c98b42d6d7fe construction uses the P2 M Ground Theory Heights  Heights Local Section Length Sum length quot smul top eq c98b42d6d7fe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PLocalSectionLengthSum.lean#L14-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PLocalSectionLengthSum.lean#L14-L41

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsLocalSectionLengthSum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsPiQuotCokerFiniteLength
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PTorsionFreeQuotientLength
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PLocalSectionLengthSum
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
open Module Submodule
open scoped Pointwise
open GroundTheory.Heights₂.Heights.LocalSectionLengthSum

theorem P2M_GroundTheory_Heights__Heights_LocalSectionLengthSum_length_quot_smul_top_eq_c98b42d6d7fe {B : Type*} [CommRing B] (I : Ideal B) (f : B) :
    Module.length B ((B ⧸ I) ⧸ (f • ⊤ : Submodule B (B ⧸ I))) =
      Module.length B (B ⧸ (I ⊔ Ideal.span {f})) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LocalSectionLengthSum».«length_quot_smul_top_eq» := P2M_GroundTheory_Heights__Heights_LocalSectionLengthSum_length_quot_smul_top_eq_c98b42d6d7fe
