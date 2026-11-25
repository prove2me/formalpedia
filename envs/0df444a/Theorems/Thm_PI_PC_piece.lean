-- Prove2me | Theorems.Thm_PI_PC_piece
-- name    : PI.PC.piece
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T05:36:06.436641+00:00
-- url     : https://prove2.me/theorems/259ead4a-d482-5f9e-8d8d-c9430cd09cb7
-- title:
--   PC: piece
-- statement:
--   The PC construction uses the piece property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ChebyshevPrimeBounds/ChebyshevPrimeBoundsLogFact.lean#L21-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ChebyshevPrimeBounds/ChebyshevPrimeBoundsLogFact.lean#L21-L41

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

theorem PI.PC.piece {p q c : ℝ} (hp : 2 ≤ p) (hpq : p ≤ q) (hc : 0 < c) (hcp : c ≤ log p) :
    ∫ t in p..q, phi t ≤ log 4 / c ^ 2 * (q - p) := by sorry
