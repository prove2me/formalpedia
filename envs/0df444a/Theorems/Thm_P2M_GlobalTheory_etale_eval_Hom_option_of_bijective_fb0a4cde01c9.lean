-- Prove2me | Theorems.Thm_P2M_GlobalTheory_etale_eval_Hom_option_of_bijective_fb0a4cde01c9
-- name    : P2M_GlobalTheory_etale_eval_Hom_option_of_bijective_fb0a4cde01c9
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T00:11:50.71988+00:00
-- url     : https://prove2.me/theorems/9f3425d2-e5d5-4eef-b318-9d5850f494b6
-- title:
--   P2 M Global Theory etale eval Hom option of bijective fb0a4cde01c9: P2 M Global Theory etale eval Hom option of bijective fb0a4cde01c9
-- statement:
--   The P2 M Global Theory etale eval Hom option of bijective fb0a4cde01c9 construction uses the P2 M Global Theory etale eval Hom option of bijective fb0a4cde01c9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/EtalePolynomialSubstitution.lean#L15-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/EtalePolynomialSubstitution.lean#L15-L48

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EtalePolynomialSubstitution
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

theorem P2M_GlobalTheory_etale_eval_Hom_option_of_bijective_fb0a4cde01c9 {k A R N : Type} [CommRing k] [CommRing A] [CommRing R] (α : k →+* A) (t : A) (f : A →+* R) (n : N → R) {d : ℕ} (e : Fin (d + 1) ≃ Option N)
    (hg : (MvPolynomial.eval₂Hom α (fun _ : Fin 1 => t)).Etale) (hΦ : Function.Bijective (MvPolynomial.eval₂Hom f n)) : (MvPolynomial.eval₂Hom (f.comp α) (fun j => (e j).elim (f t) n)).Etale := by sorry

alias «GlobalTheory».«etale_eval₂Hom_option_of_bijective» := P2M_GlobalTheory_etale_eval_Hom_option_of_bijective_fb0a4cde01c9
