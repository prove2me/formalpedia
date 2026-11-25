-- Prove2me | Theorems.Thm_PI_PrimesDyadicRS_W_small_of
-- name    : PI.PrimesDyadicRS.W.small_of
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:36:59.625558+00:00
-- url     : https://prove2.me/theorems/5437cd6d-bd1f-410b-bab6-08785c3598d8
-- title:
--   W: small of
-- statement:
--   The W construction uses the small of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DyadicPrimeIntervals/FloorHalf.lean#L13-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DyadicPrimeIntervals/FloorHalf.lean#L13-L34

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

theorem PI.PrimesDyadicRS.W.small_of (hS : SmallNat) : ∀ y : ℝ, 41 / 2 ≤ y → y < 65536 → At y := by sorry
