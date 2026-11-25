-- Prove2me | Theorems.Thm_PI_FinOrdRedOne_Core_isUnit_natCast_of_ne
-- name    : PI.FinOrdRedOne.Core.isUnit_natCast_of_ne
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T05:30:12.455622+00:00
-- url     : https://prove2.me/theorems/f73c85c8-3975-49c9-9fef-bf8aab247e5b
-- title:
--   Core: is Unit nat Cast of ne
-- statement:
--   The Core construction uses the is Unit nat Cast of ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FiniteOrderReduction/EqOneOfIsOfFinOrder.lean#L141-L157
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FiniteOrderReduction/EqOneOfIsOfFinOrder.lean#L141-L157

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

theorem PI.FinOrdRedOne.Core.isUnit_natCast_of_ne [IsLocalRing R] (p : ℕ) (hp : p.Prime)
    (hpM : (p : R) ∈ IsLocalRing.maximalIdeal R) (l : ℕ) (hl : l.Prime) (hlp : l ≠ p) :
    IsUnit (l : R) := by sorry
