-- Prove2me | Theorems.Thm_UpperTheory_exists_primitive_orthogonal_idempotents_sum_eq_of_noetherian
-- name    : UpperTheory.exists_primitive_orthogonal_idempotents_sum_eq_of_noetherian
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T11:13:24.314851+00:00
-- url     : https://prove2.me/theorems/faa3c27c-8498-4165-9550-861c98c3ff1b
-- title:
--   Upper Theory: exists primitive orthogonal idempotents sum eq of noetherian
-- statement:
--   The Upper Theory construction uses the exists primitive orthogonal idempotents sum eq of noetherian property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CMTraceForms/ExistsPrimitiveOrthogonalIdempotentsSumEqOfNoeth.lean#L26-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CMTraceForms/ExistsPrimitiveOrthogonalIdempotentsSumEqOfNoeth.lean#L26-L87

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_CMTraceForms_ExistsPrimitiveOrthogonalIdempotentsSumEqOfNoeth
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem UpperTheory.exists_primitive_orthogonal_idempotents_sum_eq_of_noetherian :
    ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (e : R), e * e = e →
      ∃ (s : ℕ) (g : Fin s → R), (∀ i, g i * g i = g i ∧ g i ≠ 0 ∧ ∀ x, x * x = x → x * g i = x → x = 0 ∨ x = g i) ∧
        (∀ i j, i ≠ j → g i * g j = 0) ∧ ∑ i, g i = e := by sorry
