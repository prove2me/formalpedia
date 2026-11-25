-- Prove2me | Theorems.Thm_PI_FinOrdRedOne_Core_eq_one_of_isOfFinOrder
-- name    : PI.FinOrdRedOne.Core.eq_one_of_isOfFinOrder
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T05:31:06.967412+00:00
-- url     : https://prove2.me/theorems/5dbbf292-02b7-4d35-a1ac-0afa36baa657
-- title:
--   Core: eq one of is Of Fin Order
-- statement:
--   The Core construction uses the eq one of is Of Fin Order property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FiniteOrderReduction/EqOneOfIsOfFinOrder.lean#L175-L201
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FiniteOrderReduction/EqOneOfIsOfFinOrder.lean#L175-L201

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FiniteOrderReduction_EqOneOfIsOfFinOrder
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.FinOrdRedOne PI.FinOrdRedOne.Core
open Matrix Finset
variable {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n]

theorem PI.FinOrdRedOne.Core.eq_one_of_isOfFinOrder [IsDomain R] [IsLocalRing R] (p : ℕ) (hp : p.Prime) (hp3 : 3 ≤ p)
    (hp0 : (p : R) ≠ 0) (hM : IsLocalRing.maximalIdeal R = Ideal.span {(p : R)})
    (hsep : ∀ x : R, (∀ k : ℕ, (p : R) ^ k ∣ x) → x = 0)
    (β : GL n R) (hfin : IsOfFinOrder β)
    (hred : (β : Matrix n n R).map (IsLocalRing.residue R) = 1) : β = 1 := by sorry
