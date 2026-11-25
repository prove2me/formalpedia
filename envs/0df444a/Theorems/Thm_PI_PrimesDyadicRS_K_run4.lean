-- Prove2me | Theorems.Thm_PI_PrimesDyadicRS_K_run4
-- name    : PI.PrimesDyadicRS.K.run4
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T05:36:08.681843+00:00
-- url     : https://prove2.me/theorems/7596f378-dd9b-4ebf-b159-c586447d6784
-- title:
--   K: run4
-- statement:
--   The K construction uses the run4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DyadicPrimeIntervals/Run4.lean#L6-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DyadicPrimeIntervals/Run4.lean#L6-L6

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DyadicPrimeIntervals_SmallLoop
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DyadicPrimeIntervals_Run4
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.PrimesDyadicRS PI.PrimesDyadicRS.K

theorem PI.PrimesDyadicRS.K.run4 : run 131072 5709 32768 98304 4388 = true := by sorry
