-- Prove2me | Theorems.Thm_PI_lp_feasible_le
-- name    : PI.lp_feasible_le
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T05:47:05.549417+00:00
-- url     : https://prove2.me/theorems/db94ab4b-2c38-452c-8697-da000af3e4fc
-- title:
--   PI: lp feasible le
-- statement:
--   The PI construction uses the lp feasible le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LinearProgramLowerBound/LpFeasibleLe.lean#L15-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LinearProgramLowerBound/LpFeasibleLe.lean#L15-L37

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

theorem PI.lp_feasible_le (l d : ℕ) [NeZero d] (Ds : ZMod d → ℝ) (hl : 2 ≤ l)
    {y : ℝ} (hy : y ∈ lpFeasible l d Ds) : y ≤ (∑ s, Ds s) / ((l : ℝ) + 1) := by sorry
