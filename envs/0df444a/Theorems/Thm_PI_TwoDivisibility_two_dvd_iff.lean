-- Prove2me | Theorems.Thm_PI_TwoDivisibility_two_dvd_iff
-- name    : PI.TwoDivisibility.two_dvd_iff
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T08:29:33.801321+00:00
-- url     : https://prove2.me/theorems/250d0a81-3d69-40ea-a767-547d9a02a3c1
-- title:
--   Two Divisibility: two dvd iff
-- statement:
--   The Two Divisibility construction uses the two dvd iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IntegerCoordinatesZero/IntCoordsZero.lean#L34-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IntegerCoordinatesZero/IntCoordsZero.lean#L34-L35

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_KerLat
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IntegerCoordinatesZero_IntCoordsZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.TwoDivisibility

theorem PI.TwoDivisibility.two_dvd_iff (p : ℤ) : (2 : ℤ) ∣ p ↔ ((p : ZMod 2) = 0) := by sorry
