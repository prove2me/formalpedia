-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_mul_span_eq_one_of_le_d361b21de1fd
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_mul_span_eq_one_of_le_d361b21de1fd
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:27:55.330645+00:00
-- url     : https://prove2.me/theorems/0e3e16e3-f282-49f5-a2a9-6c6c1240733e
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Translate Eq mul span eq one of le d361b21de1fd: P2 M Ground Theory Heights  Heights Kleiman Translate Eq mul span eq one of le d361b21de1fd
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Translate Eq mul span eq one of le d361b21de1fd construction uses the P2 M Ground Theory Heights  Heights Kleiman Translate Eq mul span eq one of le d361b21de1fd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PTwinEqBundleLocal.lean#L136-L149
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PTwinEqBundleLocal.lean#L136-L149

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_mul_span_eq_one_of_le_d361b21de1fd (hAB : A ≤ B) {L L' : Submodule A Ω} (h : L * L' = 1) :
    Submodule.span B (L : Set Ω) * Submodule.span B (L' : Set Ω) = 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«TranslateEq».«mul_span_eq_one_of_le» := P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_mul_span_eq_one_of_le_d361b21de1fd
