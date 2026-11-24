-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_span_span_of_le_5980be65a218
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_span_span_of_le_5980be65a218
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:08:20.104659+00:00
-- url     : https://prove2.me/theorems/eeaa1990-037f-4600-b965-79ed3f998ec8
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Translate Eq span span of le 5980be65a218: P2 M Ground Theory Heights  Heights Kleiman Translate Eq span span of le 5980be65a218
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Translate Eq span span of le 5980be65a218 construction uses the P2 M Ground Theory Heights  Heights Kleiman Translate Eq span span of le 5980be65a218 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PTwinEqBundleLocal.lean#L118-L128
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PTwinEqBundleLocal.lean#L118-L128

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_span_span_of_le_5980be65a218 (hAB : A ≤ B) (T : Set Ω) :
    Submodule.span B (Submodule.span A T : Set Ω) = Submodule.span B T := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«TranslateEq».«span_span_of_le» := P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_span_span_of_le_5980be65a218
