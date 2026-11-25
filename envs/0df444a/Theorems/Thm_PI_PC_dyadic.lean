-- Prove2me | Theorems.Thm_PI_PC_dyadic
-- name    : PI.PC.dyadic
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T05:35:59.853007+00:00
-- url     : https://prove2.me/theorems/b37072c8-1168-4235-94ce-9e9967c05cef
-- title:
--   PC: dyadic
-- statement:
--   The PC construction uses the dyadic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ChebyshevPrimeBounds/ChebyshevPrimeBoundsLogFact.lean#L43-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ChebyshevPrimeBounds/ChebyshevPrimeBoundsLogFact.lean#L43-L67

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

theorem PI.PC.dyadic (k : ℕ) : ∫ t in (2 : ℝ)..2 ^ (k + 1), phi t ≤
    2 / log 2 * ∑ i ∈ Finset.range k, (2 : ℝ) ^ (i + 1) / ((i : ℝ) + 1) ^ 2 := by sorry
