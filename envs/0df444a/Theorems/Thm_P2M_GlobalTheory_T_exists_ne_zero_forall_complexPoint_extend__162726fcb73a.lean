-- Prove2me | Theorems.Thm_P2M_GlobalTheory_T_exists_ne_zero_forall_complexPoint_extend__162726fcb73a
-- name    : P2M_GlobalTheory_T_exists_ne_zero_forall_complexPoint_extend__162726fcb73a
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T13:12:48.095655+00:00
-- url     : https://prove2.me/theorems/6e8e32ea-7962-4ad3-bf67-5914dbb3fa5c
-- title:
--   P2 M Global Theory T exists ne zero forall complex Point extend  162726fcb73a: P2 M Global Theory T exists ne zero forall complex Point extend  162726fcb73a
-- statement:
--   The P2 M Global Theory T exists ne zero forall complex Point extend  162726fcb73a construction uses the P2 M Global Theory T exists ne zero forall complex Point extend  162726fcb73a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsNeZeroForallComplexPointExtendStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsNeZeroForallComplexPointExtendStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsNeZeroForallComplexPointExtend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SpecialisationNumberFieldAndCountableValues
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsNeZeroForallComplexPointExtendStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem P2M_GlobalTheory_T_exists_ne_zero_forall_complexPoint_extend__162726fcb73a : ∀ (B A : Type) [CommRing B] [IsDomain B] [IsNoetherianRing B] [CommRing A] [IsDomain A] [Algebra B A] [Algebra.FiniteType B A], Function.Injective (algebraMap B A) → ∃ q : B, q ≠ 0 ∧ ∀ φ : B →+* ℂ, φ q ≠ 0 → ∃ ψ : A →+* ℂ, ψ.comp (algebraMap B A) = φ := by sorry

alias «GlobalTheory».«T».«exists_ne_zero_forall_complexPoint_extend'» := P2M_GlobalTheory_T_exists_ne_zero_forall_complexPoint_extend__162726fcb73a
