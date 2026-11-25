-- Prove2me | Theorems.Thm_PI_SqfRootsInj_W_pow_eq_part_pow_of_dvd
-- name    : PI.SqfRootsInj.W.pow_eq_part_pow_of_dvd
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:41:21.302694+00:00
-- url     : https://prove2.me/theorems/8f02476a-c135-4392-b840-a333d32d46c8
-- title:
--   W: pow eq part pow of dvd
-- statement:
--   The W construction uses the pow eq part pow of dvd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarefreeRootsInjective/WitBase.lean#L35-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarefreeRootsInjective/WitBase.lean#L35-L43

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeRootsInjective_ClaimOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeRootsInjective_WitBase
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
noncomputable section
open PI PI.SqfRootsInj PI.SqfRootsInj.W
open PI.SqfLab

theorem PI.SqfRootsInj.W.pow_eq_part_pow_of_dvd {M : Type*} [Monoid M] (ℓ : ℕ) (hℓ : ℓ.Prime) (x : M) (N : ℕ)
    (hN : N ≠ 0) (hxN : orderOf x ∣ N) :
    x ^ (ℓ ^ padicValNat ℓ N) = (primeToPart ℓ x) ^ (ℓ ^ padicValNat ℓ N) := by sorry
