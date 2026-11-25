-- Prove2me | Theorems.Thm_PI_PrimesDyadicRS_W_floor_half
-- name    : PI.PrimesDyadicRS.W.floor_half
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:36:31.323964+00:00
-- url     : https://prove2.me/theorems/e100ed89-1313-55a6-83ac-754460aabc11
-- title:
--   W: floor half
-- statement:
--   The W construction uses the floor half property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DyadicPrimeIntervals/FloorHalf.lean#L8-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DyadicPrimeIntervals/FloorHalf.lean#L8-L11

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_PrimesDyadicRS
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DyadicPrimeIntervals_ThetaDiff
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChebyshevPrimeBounds_PsiLowerBoundHolds
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DyadicPrimeIntervals_FloorHalf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.PrimesDyadicRS PI.PrimesDyadicRS.W

theorem PI.PrimesDyadicRS.W.floor_half (y : ℝ) : ⌊y⌋₊ = ⌊2 * y⌋₊ / 2 := by sorry
