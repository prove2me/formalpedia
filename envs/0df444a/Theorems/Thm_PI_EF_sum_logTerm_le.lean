-- Prove2me | Theorems.Thm_PI_EF_sum_logTerm_le
-- name    : PI.EF.sum_logTerm_le
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T05:30:21.697165+00:00
-- url     : https://prove2.me/theorems/bede5790-18ea-4e24-90ae-4cb79317aaad
-- title:
--   EF: sum log Term le
-- statement:
--   The EF construction uses the sum log Term le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/PerronSum.lean#L43-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/PerronSum.lean#L43-L70

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_GoodHeightExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_PerronSum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.EF
open Finset

theorem PI.EF.sum_logTerm_le {ε : ℝ} (hε : 0 < ε) (K : ℕ) :
    ∑ n ∈ range K, logTerm (1 + 2 * ε) n ≤ 1 / ε ^ 2 := by sorry
