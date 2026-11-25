-- Prove2me | Theorems.Thm_PI_PrimesDyadicRS_K_tstR_sound
-- name    : PI.PrimesDyadicRS.K.tstR_sound
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T05:57:16.888357+00:00
-- url     : https://prove2.me/theorems/ce9175d9-3fc4-4c37-93a4-6328b71ad2b3
-- title:
--   K: tst R sound
-- statement:
--   The K construction uses the tst R sound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DyadicPrimeIntervals/SmallNaturalNumbersBound.lean#L107-L132
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DyadicPrimeIntervals/SmallNaturalNumbersBound.lean#L107-L132

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DyadicPrimeIntervals_ThetaDiff
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DyadicPrimeIntervals_SmallLoop
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DyadicPrimeIntervals_Run1
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DyadicPrimeIntervals_Run2
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DyadicPrimeIntervals_Run3
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DyadicPrimeIntervals_Run4
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DyadicPrimeIntervals_SmallNaturalNumbersBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.PrimesDyadicRS PI.PrimesDyadicRS.K
open Real

theorem PI.PrimesDyadicRS.K.tstR_sound {h d : ℕ} (ht : tstR h d = true) (h2 : 2 ≤ h) :
    3 * ((h : ℝ) + 1) < 10 * (d : ℝ) * Real.log ((h : ℝ) / 2) := by sorry
