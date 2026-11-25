-- Prove2me | Theorems.Thm_P2M_GlobalTheory_T_exists_perm_of_sum_monomial_eq__0e5b55daf26f
-- name    : P2M_GlobalTheory_T_exists_perm_of_sum_monomial_eq__0e5b55daf26f
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T00:10:07.474913+00:00
-- url     : https://prove2.me/theorems/6af468ad-f5db-4daf-8389-08c8d1eef1ee
-- title:
--   P2 M Global Theory T exists perm of sum monomial eq  0e5b55daf26f: P2 M Global Theory T exists perm of sum monomial eq  0e5b55daf26f
-- statement:
--   The P2 M Global Theory T exists perm of sum monomial eq  0e5b55daf26f construction uses the P2 M Global Theory T exists perm of sum monomial eq  0e5b55daf26f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsPermOfSumMonomialEqStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsPermOfSumMonomialEqStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsPermOfSumMonomialEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsPermOfSumMonomialEqStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
set_option maxHeartbeats 1000000

theorem P2M_GlobalTheory_T_exists_perm_of_sum_monomial_eq__0e5b55daf26f : ∀ (ι S : Type) [Fintype ι] [Fintype S] (x y : ι → S → ℂ), (∀ μ : S → ℕ, ∑ i, ∏ s, x i s ^ μ s = ∑ i, ∏ s, y i s ^ μ s) → ∃ ρ : Equiv.Perm ι, ∀ i, x i = y (ρ i) := by sorry

alias «GlobalTheory».«T».«exists_perm_of_sum_monomial_eq'» := P2M_GlobalTheory_T_exists_perm_of_sum_monomial_eq__0e5b55daf26f
