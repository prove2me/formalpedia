-- Prove2me | Theorems.Thm_P2M_GlobalTheory_T_exists_orthogonal_idempotents_of_sum_mul_eq_one__9dc073da72ca
-- name    : P2M_GlobalTheory_T_exists_orthogonal_idempotents_of_sum_mul_eq_one__9dc073da72ca
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T13:06:18.889663+00:00
-- url     : https://prove2.me/theorems/85d41861-2276-50ea-9b62-9d48865d59f3
-- title:
--   P2 M Global Theory T exists orthogonal idempotents of sum mul eq one  9dc073da72ca: P2 M Global Theory T exists orthogonal idempotents of sum mul eq one  9dc073da72ca
-- statement:
--   The P2 M Global Theory T exists orthogonal idempotents of sum mul eq one  9dc073da72ca construction uses the P2 M Global Theory T exists orthogonal idempotents of sum mul eq one  9dc073da72ca property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ExistsOrthogonalIdempotentsOfSumMulEqOneStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ExistsOrthogonalIdempotentsOfSumMulEqOneStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsOrthogonalIdempotentsOfSumMulEqOne
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsOrthogonalIdempotentsOfSumMulEqOneStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem P2M_GlobalTheory_T_exists_orthogonal_idempotents_of_sum_mul_eq_one__9dc073da72ca : ∀ (F : Type) [Field F] [NumberField F] (ι : Type) [Fintype ι] (f s : ι → NumberField.AdeleRing (NumberField.RingOfIntegers F) F), ∑ i, s i * f i = 1 → ∃ e t : ι → NumberField.AdeleRing (NumberField.RingOfIntegers F) F, ∑ i, e i = 1 ∧ (∀ i j, i ≠ j → e i * e j = 0) ∧ ∀ i, t i * f i = e i := by sorry

alias «GlobalTheory».«T».«exists_orthogonal_idempotents_of_sum_mul_eq_one'» := P2M_GlobalTheory_T_exists_orthogonal_idempotents_of_sum_mul_eq_one__9dc073da72ca
