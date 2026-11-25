-- Prove2me | Theorems.Thm_P2M_GlobalTheory_T_exists_eq_const_mul_of_forall_exists_norm_eq__22882968d2af
-- name    : P2M_GlobalTheory_T_exists_eq_const_mul_of_forall_exists_norm_eq__22882968d2af
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T13:07:12.115464+00:00
-- url     : https://prove2.me/theorems/c964a9bb-e3f7-4045-aca7-423396e7fcd6
-- title:
--   P2 M Global Theory T exists eq const mul of forall exists norm eq  22882968d2af: P2 M Global Theory T exists eq const mul of forall exists norm eq  22882968d2af
-- statement:
--   The P2 M Global Theory T exists eq const mul of forall exists norm eq  22882968d2af construction uses the P2 M Global Theory T exists eq const mul of forall exists norm eq  22882968d2af property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ExistsEqConstMulOfForallExistsNormEqStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ExistsEqConstMulOfForallExistsNormEqStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsEqConstMulOfForallExistsNormEq
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_EqZeroOfMulEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsEqConstMulOfForallExistsNormEqStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem P2M_GlobalTheory_T_exists_eq_const_mul_of_forall_exists_norm_eq__22882968d2af : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] (ι : Type) [Countable ι] (O : Set V), IsOpen O → IsPreconnected O → O.Nonempty → ∀ (P : V → ℂ) (Q : ι → V → ℂ), DifferentiableOn ℂ P O → (∀ i, DifferentiableOn ℂ (Q i) O) → (∀ x ∈ O, ∃ i, ‖P x‖ = ‖Q i x‖) → ∃ (i : ι) (c : ℂ), ∀ x ∈ O, P x = c * Q i x := by sorry

alias «GlobalTheory».«T».«exists_eq_const_mul_of_forall_exists_norm_eq'» := P2M_GlobalTheory_T_exists_eq_const_mul_of_forall_exists_norm_eq__22882968d2af
