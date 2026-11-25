-- Prove2me | Theorems.Thm_P2M_GlobalTheory_T_exists_minimal_local_generators__df6d77594245
-- name    : P2M_GlobalTheory_T_exists_minimal_local_generators__df6d77594245
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T00:10:05.503117+00:00
-- url     : https://prove2.me/theorems/43ac4f90-fe5c-484c-9ca1-ecf165a0e308
-- title:
--   P2 M Global Theory T exists minimal local generators  df6d77594245: P2 M Global Theory T exists minimal local generators  df6d77594245
-- statement:
--   The P2 M Global Theory T exists minimal local generators  df6d77594245 construction uses the P2 M Global Theory T exists minimal local generators  df6d77594245 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsMinimalLocalGeneratorsStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsMinimalLocalGeneratorsStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsMinimalLocalGenerators
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsMinimalLocalGeneratorsStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing TensorProduct
set_option maxHeartbeats 1000000

theorem P2M_GlobalTheory_T_exists_minimal_local_generators__df6d77594245 : ∀ (S : Type) [CommRing S] [IsNoetherianRing S] (Q : Ideal S) [Q.IsPrime], ∃ (h : ℕ) (f : Fin h → S) (g : S), g ∉ Q ∧ (∀ j, f j ∈ Q) ∧ (∀ x ∈ Q, g * x ∈ Ideal.span (Set.range f)) ∧ h = (maximalIdeal (Localization.AtPrime Q)).spanFinrank ∧ ∀ (a : Fin h → S) (u : S), u ∉ Q → u * ∑ j, a j * f j ∈ Q ^ 2 → ∀ j, a j ∈ Q := by sorry

alias «GlobalTheory».«T».«exists_minimal_local_generators'» := P2M_GlobalTheory_T_exists_minimal_local_generators__df6d77594245
