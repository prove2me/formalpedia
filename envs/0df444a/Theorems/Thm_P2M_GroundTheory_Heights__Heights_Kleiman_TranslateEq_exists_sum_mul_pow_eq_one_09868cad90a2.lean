-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_exists_sum_mul_pow_eq_one_09868cad90a2
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_exists_sum_mul_pow_eq_one_09868cad90a2
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T03:27:36.204522+00:00
-- url     : https://prove2.me/theorems/9d73e5fa-a2b6-4ebe-987f-5eba63e71520
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Translate Eq exists sum mul pow eq one 09868cad90a2: P2 M Ground Theory Heights  Heights Kleiman Translate Eq exists sum mul pow eq one 09868cad90a2
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Translate Eq exists sum mul pow eq one 09868cad90a2 construction uses the P2 M Ground Theory Heights  Heights Kleiman Translate Eq exists sum mul pow eq one 09868cad90a2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PTwinEqBundleLocal.lean#L14-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PTwinEqBundleLocal.lean#L14-L26

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
variable (A : Subalgebra S Ω) {k : ℕ} (f c : Fin k → Ω)

theorem P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_exists_sum_mul_pow_eq_one_09868cad90a2 (hf : ∀ l, f l ∈ A) (hc : ∀ l, c l ∈ A) (hs : ∑ l, c l * f l = 1)
    (n : ℕ) : ∃ d : Fin k → Ω, (∀ l, d l ∈ A) ∧ ∑ l, d l * f l ^ n = 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«TranslateEq».«exists_sum_mul_pow_eq_one» := P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_exists_sum_mul_pow_eq_one_09868cad90a2
