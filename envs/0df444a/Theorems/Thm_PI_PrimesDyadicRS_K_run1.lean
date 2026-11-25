-- Prove2me | Theorems.Thm_PI_PrimesDyadicRS_K_run1
-- name    : PI.PrimesDyadicRS.K.run1
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T05:36:45.600611+00:00
-- url     : https://prove2.me/theorems/f9eccc53-9d4a-4e4f-b4b8-1d1f64668ef5
-- title:
--   K: run1
-- statement:
--   The K construction uses the run1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DyadicPrimeIntervals/Run1.lean#L6-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DyadicPrimeIntervals/Run1.lean#L6-L6

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DyadicPrimeIntervals_SmallLoop
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DyadicPrimeIntervals_Run1
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.PrimesDyadicRS PI.PrimesDyadicRS.K

theorem PI.PrimesDyadicRS.K.run1 : run 32768 1612 32766 2 1 = true := by sorry
