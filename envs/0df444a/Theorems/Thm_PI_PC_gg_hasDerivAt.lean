-- Prove2me | Theorems.Thm_PI_PC_gg_hasDerivAt
-- name    : PI.PC.gg_hasDerivAt
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T05:36:02.349439+00:00
-- url     : https://prove2.me/theorems/6d9f1bb9-d450-4257-bb98-3be6d999774d
-- title:
--   PC: gg has Deriv At
-- statement:
--   The PC construction uses the gg has Deriv At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ChebyshevPrimeBounds/ChebyshevPrimeBoundsLogFact.lean#L85-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ChebyshevPrimeBounds/ChebyshevPrimeBoundsLogFact.lean#L85-L99

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChebyshevPrimeBounds_PrimeCountBoundOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChebyshevPrimeBounds_ChebyshevPrimeBoundsLogFact
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
open Real MeasureTheory Set

theorem PI.PC.gg_hasDerivAt {t : ℝ} (ht : 1 < t) : HasDerivAt gg (gg' t) t := by sorry
