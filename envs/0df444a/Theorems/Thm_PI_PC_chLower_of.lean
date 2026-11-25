-- Prove2me | Theorems.Thm_PI_PC_chLower_of
-- name    : PI.PC.chLower_of
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T05:35:56.318534+00:00
-- url     : https://prove2.me/theorems/0e861c1e-fbef-55c6-a1bb-53e04394c463
-- title:
--   PC: ch Lower of
-- statement:
--   The PC construction uses the ch Lower of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ChebyshevPrimeBounds/PrimeCountBoundOf.lean#L43-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ChebyshevPrimeBounds/PrimeCountBoundOf.lean#L43-L48

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_PrimeCount
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChebyshevPrimeBounds_PrimeCountBoundOf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.PC
open Real

theorem PI.PC.chLower_of (hA : ANum) (hD : DLower) (hS : Sandwich) : CHLower := by sorry
