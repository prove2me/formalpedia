-- Prove2me | Theorems.Thm_PI_PrimesDyadicRS_K_run2
-- name    : PI.PrimesDyadicRS.K.run2
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T05:36:40.415865+00:00
-- url     : https://prove2.me/theorems/41d5a94f-18d9-4752-9efb-cdf6702efa47
-- title:
--   K: run2
-- statement:
--   The K construction uses the run2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DyadicPrimeIntervals/Run2.lean#L6-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DyadicPrimeIntervals/Run2.lean#L6-L6

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DyadicPrimeIntervals_SmallLoop
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DyadicPrimeIntervals_Run2
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.PrimesDyadicRS PI.PrimesDyadicRS.K

theorem PI.PrimesDyadicRS.K.run2 : run 65536 3030 32768 32768 1612 = true := by sorry
