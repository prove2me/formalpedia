-- Prove2me | Theorems.Thm_PI_FinOrdRedOne_Core_one_add_pow_eq
-- name    : PI.FinOrdRedOne.Core.one_add_pow_eq
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T05:30:18.325115+00:00
-- url     : https://prove2.me/theorems/4cf7de02-e843-4387-94e7-8020c81ff34d
-- title:
--   Core: one add pow eq
-- statement:
--   The Core construction uses the one add pow eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FiniteOrderReduction/EqOneOfIsOfFinOrder.lean#L50-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FiniteOrderReduction/EqOneOfIsOfFinOrder.lean#L50-L56

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

theorem PI.FinOrdRedOne.Core.one_add_pow_eq (D : Matrix n n R) (k : ℕ) :
    (1 + D) ^ (k + 2) = ∑ i ∈ range (k + 1), (k + 2).choose (i + 2) • D ^ (i + 2)
      + (k + 2) • D + 1 := by sorry
