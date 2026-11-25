-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_mem_of_forall_pow_mul_mem_e651439d42d9
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_mem_of_forall_pow_mul_mem_e651439d42d9
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:27:51.963998+00:00
-- url     : https://prove2.me/theorems/d7213c72-11ad-48fc-9554-46a5a4170354
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Translate Eq mem of forall pow mul mem e651439d42d9: P2 M Ground Theory Heights  Heights Kleiman Translate Eq mem of forall pow mul mem e651439d42d9
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Translate Eq mem of forall pow mul mem e651439d42d9 construction uses the P2 M Ground Theory Heights  Heights Kleiman Translate Eq mem of forall pow mul mem e651439d42d9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PTwinEqBundleLocal.lean#L28-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PTwinEqBundleLocal.lean#L28-L42

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_mem_of_forall_pow_mul_mem_e651439d42d9 (hf : ∀ l, f l ∈ A) (hc : ∀ l, c l ∈ A) (hs : ∑ l, c l * f l = 1)
    (P : Submodule A Ω) {z : Ω} (hz : ∀ l, ∃ m : ℕ, f l ^ m * z ∈ P) : z ∈ P := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«TranslateEq».«mem_of_forall_pow_mul_mem» := P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_mem_of_forall_pow_mul_mem_e651439d42d9
