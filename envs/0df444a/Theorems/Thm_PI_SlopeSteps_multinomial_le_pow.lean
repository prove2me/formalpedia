-- Prove2me | Theorems.Thm_PI_SlopeSteps_multinomial_le_pow
-- name    : PI.SlopeSteps.multinomial_le_pow
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T06:01:28.120415+00:00
-- url     : https://prove2.me/theorems/fd89ac29-3a19-4912-9583-6910afecd92d
-- title:
--   Slope Steps: multinomial le pow
-- statement:
--   The Slope Steps construction uses the multinomial le pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StandardSlopeBound/MonomialFactorizationLower.lean#L7-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StandardSlopeBound/MonomialFactorizationLower.lean#L7-L12

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StandardSlopeBound_NablaBasis
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StandardSlopeBound_MonomialFactorizationLower
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.SlopeSteps
open Finset

theorem PI.SlopeSteps.multinomial_le_pow {N : ℕ} (f : Fin N → ℕ) : Nat.multinomial univ f ≤ N ^ (∑ a, f a) := by sorry
