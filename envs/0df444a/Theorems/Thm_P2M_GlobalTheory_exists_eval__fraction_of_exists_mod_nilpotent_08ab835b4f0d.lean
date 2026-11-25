-- Prove2me | Theorems.Thm_P2M_GlobalTheory_exists_eval__fraction_of_exists_mod_nilpotent_08ab835b4f0d
-- name    : P2M_GlobalTheory_exists_eval__fraction_of_exists_mod_nilpotent_08ab835b4f0d
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T00:12:10.831604+00:00
-- url     : https://prove2.me/theorems/5f35664b-4c24-47c3-b9e8-a5ae9df549a5
-- title:
--   P2 M Global Theory exists eval  fraction of exists mod nilpotent 08ab835b4f0d: P2 M Global Theory exists eval  fraction of exists mod nilpotent 08ab835b4f0d
-- statement:
--   The P2 M Global Theory exists eval  fraction of exists mod nilpotent 08ab835b4f0d construction uses the P2 M Global Theory exists eval  fraction of exists mod nilpotent 08ab835b4f0d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LocalizedPresentationEvalQuotientFraction.lean#L7-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LocalizedPresentationEvalQuotientFraction.lean#L7-L85

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LocalizedPresentationEvalQuotientFraction
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open MvPolynomial

theorem P2M_GlobalTheory_exists_eval__fraction_of_exists_mod_nilpotent_08ab835b4f0d : ∀ (R B : Type) [CommRing R] [CommRing B] (c : R →+* B) (J : Ideal R) (n : ℕ), (∀ x ∈ J ^ n, c x = 0) → ∀ (m : ℕ) (r : Fin m → B), (∀ g : B, ∃ P Q : MvPolynomial (Fin m) R, IsUnit (MvPolynomial.eval₂ c r Q) ∧ g * MvPolynomial.eval₂ c r Q - MvPolynomial.eval₂ c r P ∈ Ideal.map c J) → ∀ g : B, ∃ P Q : MvPolynomial (Fin m) R, IsUnit (MvPolynomial.eval₂ c r Q) ∧ g * MvPolynomial.eval₂ c r Q = MvPolynomial.eval₂ c r P := by sorry

alias «GlobalTheory».«exists_eval₂_fraction_of_exists_mod_nilpotent» := P2M_GlobalTheory_exists_eval__fraction_of_exists_mod_nilpotent_08ab835b4f0d
