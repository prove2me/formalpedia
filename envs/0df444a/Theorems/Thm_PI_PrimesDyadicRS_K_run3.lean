-- Prove2me | Theorems.Thm_PI_PrimesDyadicRS_K_run3
-- name    : PI.PrimesDyadicRS.K.run3
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:35:58.333329+00:00
-- url     : https://prove2.me/theorems/e32059fc-6d1f-54f9-bea9-44450af04f37
-- title:
--   K: run3
-- statement:
--   The K construction uses the run3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DyadicPrimeIntervals/Run3.lean#L6-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DyadicPrimeIntervals/Run3.lean#L6-L6

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DyadicPrimeIntervals_SmallLoop
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DyadicPrimeIntervals_Run3
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.PrimesDyadicRS PI.PrimesDyadicRS.K

theorem PI.PrimesDyadicRS.K.run3 : run 98304 4388 32768 65536 3030 = true := by sorry
