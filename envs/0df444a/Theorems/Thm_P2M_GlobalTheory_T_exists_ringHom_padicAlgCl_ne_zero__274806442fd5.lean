-- Prove2me | Theorems.Thm_P2M_GlobalTheory_T_exists_ringHom_padicAlgCl_ne_zero__274806442fd5
-- name    : P2M_GlobalTheory_T_exists_ringHom_padicAlgCl_ne_zero__274806442fd5
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T13:07:31.607127+00:00
-- url     : https://prove2.me/theorems/5a59acde-776d-4d72-b037-95b374656ee5
-- title:
--   P2 M Global Theory T exists ring Hom padic Alg Cl ne zero  274806442fd5: P2 M Global Theory T exists ring Hom padic Alg Cl ne zero  274806442fd5
-- statement:
--   The P2 M Global Theory T exists ring Hom padic Alg Cl ne zero  274806442fd5 construction uses the P2 M Global Theory T exists ring Hom padic Alg Cl ne zero  274806442fd5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsRingHomPadicAlgClNeZeroStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsRingHomPadicAlgClNeZeroStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsRingHomPadicAlgClNeZero
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsRingHomPadicAlgClNeZeroStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
set_option maxHeartbeats 1000000

theorem P2M_GlobalTheory_T_exists_ringHom_padicAlgCl_ne_zero__274806442fd5 : ∀ (B : Type) [CommRing B] [IsDomain B] [IsLocalRing B] [IsNoetherianRing B] [CharZero B], Finite (ResidueField B) → ∀ h : B, h ≠ 0 → ∃ (p : ℕ) (_ : Fact p.Prime) (χ : B →+* PadicAlgCl p), (∀ b, ‖χ b‖ ≤ 1) ∧ (∀ b ∈ maximalIdeal B, ‖χ b‖ < 1) ∧ χ h ≠ 0 := by sorry

alias «GlobalTheory».«T».«exists_ringHom_padicAlgCl_ne_zero'» := P2M_GlobalTheory_T_exists_ringHom_padicAlgCl_ne_zero__274806442fd5
