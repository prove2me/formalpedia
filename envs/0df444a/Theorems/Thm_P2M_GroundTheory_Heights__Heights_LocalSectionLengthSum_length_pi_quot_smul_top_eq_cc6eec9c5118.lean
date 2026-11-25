-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LocalSectionLengthSum_length_pi_quot_smul_top_eq_cc6eec9c5118
-- name    : P2M_GroundTheory_Heights__Heights_LocalSectionLengthSum_length_pi_quot_smul_top_eq_cc6eec9c5118
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T03:27:57.065992+00:00
-- url     : https://prove2.me/theorems/d6f42e48-c406-46bd-a27d-323fa5a07840
-- title:
--   P2 M Ground Theory Heights  Heights Local Section Length Sum length pi quot smul top eq cc6eec9c5118: P2 M Ground Theory Heights  Heights Local Section Length Sum length pi quot smul top eq cc6eec9c51
-- statement:
--   The P2 M Ground Theory Heights  Heights Local Section Length Sum length pi quot smul top eq cc6eec9c5118 construction uses the P2 M Ground Theory Heights  Heights Local Section Length Sum length pi quot smul top eq cc6eec9c5118 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PLocalSectionLengthSum.lean#L43-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PLocalSectionLengthSum.lean#L43-L66

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

theorem P2M_GroundTheory_Heights__Heights_LocalSectionLengthSum_length_pi_quot_smul_top_eq_cc6eec9c5118 {B ι : Type*} [CommRing B] [Fintype ι] (M : ι → Type*)
    [∀ i, AddCommGroup (M i)] [∀ i, Module B (M i)] (f : B) :
    Module.length B ((Π i, M i) ⧸ (f • ⊤ : Submodule B (Π i, M i))) =
      ∑ i, Module.length B (M i ⧸ (f • ⊤ : Submodule B (M i))) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LocalSectionLengthSum».«length_pi_quot_smul_top_eq» := P2M_GroundTheory_Heights__Heights_LocalSectionLengthSum_length_pi_quot_smul_top_eq_cc6eec9c5118
