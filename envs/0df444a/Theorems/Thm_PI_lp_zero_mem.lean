-- Prove2me | Theorems.Thm_PI_lp_zero_mem
-- name    : PI.lp_zero_mem
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T05:47:14.71146+00:00
-- url     : https://prove2.me/theorems/e139765d-0f02-48cf-9a26-43f71afba451
-- title:
--   PI: lp zero mem
-- statement:
--   The PI construction uses the lp zero mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LinearProgramLowerBound/LpFeasibleLe.lean#L39-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LinearProgramLowerBound/LpFeasibleLe.lean#L39-L41

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LpLower
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LinearProgramLowerBound_LpFeasibleLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI
open Finset

theorem PI.lp_zero_mem (l d : ℕ) [NeZero d] (Ds : ZMod d → ℝ) (hD : ∀ s, 0 ≤ Ds s) :
    (0 : ℝ) ∈ lpFeasible l d Ds := by sorry
