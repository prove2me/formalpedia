-- Prove2me | Theorems.Thm_PI_HookSteps_prod_factorial_le
-- name    : PI.HookSteps.prod_factorial_le
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T08:17:17.573937+00:00
-- url     : https://prove2.me/theorems/6b19b812-916e-4e89-befe-dec9327bb2de
-- title:
--   Hook Steps: prod factorial le
-- statement:
--   The Hook Steps construction uses the prod factorial le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HookLengthBound/ProdFactorialLe.lean#L25-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HookLengthBound/ProdFactorialLe.lean#L25-L35

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HookLengthBound_DetShiftNormOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HookLengthBound_DiagonalMonomialFactorial
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HookLengthBound_ProdFactorialLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Formalism.GradedWeylDivisibility
noncomputable section
open PI PI.HookSteps

theorem PI.HookSteps.prod_factorial_le (N : ℕ) (hN : 0 < N) (ν : Fin N → ℕ) (hν : Antitone ν) :
    ∏ i : Fin N, (ν i + (N - 1 - i)).factorial ≤
      (∏ i, (ν i).factorial) * (ν ⟨0, hN⟩ + N) ^ (N * (N - 1) / 2) := by sorry
