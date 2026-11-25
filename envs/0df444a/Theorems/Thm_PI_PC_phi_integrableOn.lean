-- Prove2me | Theorems.Thm_PI_PC_phi_integrableOn
-- name    : PI.PC.phi_integrableOn
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T05:35:51.910753+00:00
-- url     : https://prove2.me/theorems/c4acd921-8cc5-4836-8740-3efcf1bb628b
-- title:
--   PC: phi integrable On
-- statement:
--   The PC construction uses the phi integrable On property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ChebyshevPrimeBounds/ChebyshevPrimeBoundsLogFact.lean#L12-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ChebyshevPrimeBounds/ChebyshevPrimeBoundsLogFact.lean#L12-L15

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

theorem PI.PC.phi_integrableOn {p : ℝ} (q : ℝ) (hp : 2 ≤ p) : IntegrableOn phi (Icc p q) volume := by sorry
