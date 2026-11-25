-- Prove2me | Theorems.Thm_PI_lp_shift_sum
-- name    : PI.lp_shift_sum
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T05:46:56.150029+00:00
-- url     : https://prove2.me/theorems/09089d00-dafd-547b-b40e-e2a35c5fed7e
-- title:
--   PI: lp shift sum
-- statement:
--   The PI construction uses the lp shift sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LinearProgramLowerBound/LpFeasibleLe.lean#L8-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LinearProgramLowerBound/LpFeasibleLe.lean#L8-L13

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

theorem PI.lp_shift_sum (d : ℕ) [NeZero d] (xs : ZMod d → ℕ → ℝ) :
    ∑ s, ∑ i ∈ range d, xs (s - (i : ZMod d)) i = ∑ s, ∑ i ∈ range d, xs s i := by sorry
