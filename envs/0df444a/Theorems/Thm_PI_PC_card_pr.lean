-- Prove2me | Theorems.Thm_PI_PC_card_pr
-- name    : PI.PC.card_pr
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T05:35:51.452544+00:00
-- url     : https://prove2.me/theorems/a6ae3f8a-c398-48d0-b6c0-9cdad341a715
-- title:
--   PC: card pr
-- statement:
--   The PC construction uses the card pr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ChebyshevPrimeBounds/ChebyshevPrimeBoundsLogFact.lean#L154-L157
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ChebyshevPrimeBounds/ChebyshevPrimeBoundsLogFact.lean#L154-L157

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

theorem PI.PC.card_pr (y : ℝ) : (pr y).card = Nat.primeCounting ⌊y⌋₊ := by sorry
