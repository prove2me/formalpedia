-- Prove2me | Theorems.Thm_PI_SqfRootsInj_W_pow_eq_part_pow
-- name    : PI.SqfRootsInj.W.pow_eq_part_pow
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T08:28:24.204774+00:00
-- url     : https://prove2.me/theorems/76a6a487-7a62-5a52-aa10-5e481923e39a
-- title:
--   W: pow eq part pow
-- statement:
--   The W construction uses the pow eq part pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarefreeRootsInjective/WitBase.lean#L11-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarefreeRootsInjective/WitBase.lean#L11-L33

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

theorem PI.SqfRootsInj.W.pow_eq_part_pow {M : Type*} [Monoid M] (ℓ : ℕ) (hℓ : ℓ.Prime) (x : M)
    (hx : 0 < orderOf x) :
    x ^ (ℓ ^ (orderOf x).factorization ℓ) =
      (primeToPart ℓ x) ^ (ℓ ^ (orderOf x).factorization ℓ) := by sorry
