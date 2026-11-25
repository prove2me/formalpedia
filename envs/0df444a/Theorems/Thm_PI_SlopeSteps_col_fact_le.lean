-- Prove2me | Theorems.Thm_PI_SlopeSteps_col_fact_le
-- name    : PI.SlopeSteps.col_fact_le
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T06:01:06.255126+00:00
-- url     : https://prove2.me/theorems/04022f5b-68f5-492d-989c-13b28c5a77c3
-- title:
--   Slope Steps: col fact le
-- statement:
--   The Slope Steps construction uses the col fact le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StandardSlopeBound/MonomialFactorizationLower.lean#L14-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StandardSlopeBound/MonomialFactorizationLower.lean#L14-L17

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

theorem PI.SlopeSteps.col_fact_le {N : ℕ} (f : Fin N → ℕ) :
    (∑ a, f a).factorial ≤ N ^ (∑ a, f a) * ∏ a, (f a).factorial := by sorry
