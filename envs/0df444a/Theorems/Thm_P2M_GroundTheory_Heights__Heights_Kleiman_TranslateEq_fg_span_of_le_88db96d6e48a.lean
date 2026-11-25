-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_fg_span_of_le_88db96d6e48a
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_fg_span_of_le_88db96d6e48a
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T03:27:55.452469+00:00
-- url     : https://prove2.me/theorems/eee34efa-2e43-4319-80d2-c62933c9f8fb
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Translate Eq fg span of le 88db96d6e48a: P2 M Ground Theory Heights  Heights Kleiman Translate Eq fg span of le 88db96d6e48a
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Translate Eq fg span of le 88db96d6e48a construction uses the P2 M Ground Theory Heights  Heights Kleiman Translate Eq fg span of le 88db96d6e48a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PTwinEqBundleLocal.lean#L130-L134
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PTwinEqBundleLocal.lean#L130-L134

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTwinEqBundleLocal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman GroundTheory.Heights₂.Heights.Kleiman.TranslateEq
open scoped Pointwise
variable {S : Type*} [CommRing S] {Ω : Type*} [Field Ω] [Algebra S Ω]
variable {A B : Subalgebra S Ω}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_fg_span_of_le_88db96d6e48a (hAB : A ≤ B) {L : Submodule A Ω} (hL : L.FG) :
    (Submodule.span B (L : Set Ω)).FG := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«TranslateEq».«fg_span_of_le» := P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_fg_span_of_le_88db96d6e48a
