-- Prove2me | Theorems.Thm_PI_SqfPrimeFactor_W_ana_three
-- name    : PI.SqfPrimeFactor.W.ana_three
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T08:26:17.73517+00:00
-- url     : https://prove2.me/theorems/f404bcf8-3111-4299-ab76-9fd64e53d5cb
-- title:
--   W: ana three
-- statement:
--   The W construction uses the ana three property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarefreePrimeFactor/AnaCore.lean#L30-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarefreePrimeFactor/AnaCore.lean#L30-L49

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_PrimesDyadicRS
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreePrimeFactor_AnaCore
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.SqfPrimeFactor PI.SqfPrimeFactor.W
open Finset

theorem PI.SqfPrimeFactor.W.ana_three (r : ℕ) (hr : 100 ≤ r) :
    (({r - 2, r - 1, r} : Finset ℕ).filter Nat.Prime).card ≤ 2 := by sorry
