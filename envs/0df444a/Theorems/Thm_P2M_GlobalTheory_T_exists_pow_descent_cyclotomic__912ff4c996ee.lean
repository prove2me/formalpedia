-- Prove2me | Theorems.Thm_P2M_GlobalTheory_T_exists_pow_descent_cyclotomic__912ff4c996ee
-- name    : P2M_GlobalTheory_T_exists_pow_descent_cyclotomic__912ff4c996ee
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T00:10:19.305805+00:00
-- url     : https://prove2.me/theorems/07a3ca24-5679-417b-96ee-04d377adb68d
-- title:
--   P2 M Global Theory T exists pow descent cyclotomic  912ff4c996ee: P2 M Global Theory T exists pow descent cyclotomic  912ff4c996ee
-- statement:
--   The P2 M Global Theory T exists pow descent cyclotomic  912ff4c996ee construction uses the P2 M Global Theory T exists pow descent cyclotomic  912ff4c996ee property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsPowDescentCyclotomicStatement.lean#L6-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsPowDescentCyclotomicStatement.lean#L6-L9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsPowDescentCyclotomic
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsPowDescentCyclotomicStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
set_option maxHeartbeats 1000000

theorem P2M_GlobalTheory_T_exists_pow_descent_cyclotomic__912ff4c996ee : ∀ (E : Type) [Field E] [NumberField E] (l r : ℕ), l.Prime → ∃ M : ℕ, 0 < M ∧ l ^ r ∣ M ∧
    ∀ (Ω : Type) [Field Ω] [Algebra E Ω] (ζ : Ω), IsPrimitiveRoot ζ M → ∀ (u : E) (w : Ω),
      w ∈ IntermediateField.adjoin E {ζ} → w ^ M = algebraMap E Ω u → ∃ v : E, v ^ (l ^ r) = u := by sorry

alias «GlobalTheory».«T».«exists_pow_descent_cyclotomic'» := P2M_GlobalTheory_T_exists_pow_descent_cyclotomic__912ff4c996ee
