-- Prove2me | Theorems.Thm_P2M_GlobalTheory_T_exists_algebraMap_sub_eq_sum_conjugates__8f225b3c9a0f
-- name    : P2M_GlobalTheory_T_exists_algebraMap_sub_eq_sum_conjugates__8f225b3c9a0f
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T15:34:02.134392+00:00
-- url     : https://prove2.me/theorems/21dc82c6-0177-452c-9352-db067c225030
-- title:
--   P2 M Global Theory T exists algebra Map sub eq sum conjugates  8f225b3c9a0f: P2 M Global Theory T exists algebra Map sub eq sum conjugates  8f225b3c9a0f
-- statement:
--   The P2 M Global Theory T exists algebra Map sub eq sum conjugates  8f225b3c9a0f construction uses the P2 M Global Theory T exists algebra Map sub eq sum conjugates  8f225b3c9a0f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsAlgebraMapSubEqSumConjugatesStatement.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsAlgebraMapSubEqSumConjugatesStatement.lean#L8-L9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsAlgebraMapSubEqSumConjugates
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_ExistsNotCongPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsAlgebraMapSubEqSumConjugatesStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open scoped Pointwise
set_option maxHeartbeats 1000000

theorem P2M_GlobalTheory_T_exists_algebraMap_sub_eq_sum_conjugates__8f225b3c9a0f : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (y : Ω), ∃ (e : E) (s : Finset Ω), (∀ x ∈ s, x ≠ y ∧ ∃ σ : G E Ω, σ y = x) ∧ algebraMap E Ω e - y = ∑ x ∈ s, x := by sorry

alias «GlobalTheory».«T».«exists_algebraMap_sub_eq_sum_conjugates'» := P2M_GlobalTheory_T_exists_algebraMap_sub_eq_sum_conjugates__8f225b3c9a0f
