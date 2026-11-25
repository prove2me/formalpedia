-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_fg_and_invertible_of_frame_f159bf763875
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_fg_and_invertible_of_frame_f159bf763875
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:27:36.755052+00:00
-- url     : https://prove2.me/theorems/aed14ccc-ce4d-4f9d-b870-e88690a6d1a4
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Translate Eq fg and invertible of frame f159bf763875: P2 M Ground Theory Heights  Heights Kleiman Translate Eq fg and invertible of frame f159bf763875
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Translate Eq fg and invertible of frame f159bf763875 construction uses the P2 M Ground Theory Heights  Heights Kleiman Translate Eq fg and invertible of frame f159bf763875 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PTwinEqBundleLocal.lean#L44-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PTwinEqBundleLocal.lean#L44-L110

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_fg_and_invertible_of_frame_f159bf763875 (L : Submodule A Ω) (b : Fin k → Ω)
    (hf : ∀ l, f l ∈ A) (hc : ∀ l, c l ∈ A) (hs : ∑ l, c l * f l = 1) (hb : ∀ l, b l ≠ 0)
    (hL : ∀ l e, (∃ n : ℕ, f l ^ n * e ∈ L) ↔ ∃ a : Ω, (∃ n : ℕ, f l ^ n * a ∈ A) ∧ e = a * b l) :
    L.FG ∧ ∃ L' : Submodule A Ω, L * L' = 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«TranslateEq».«fg_and_invertible_of_frame» := P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_fg_and_invertible_of_frame_f159bf763875
