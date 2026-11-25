-- Prove2me | Theorems.Thm_PI_Residue_sum_range_le
-- name    : PI.Residue.sum_range_le
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T08:19:57.678814+00:00
-- url     : https://prove2.me/theorems/c05aa191-e56d-481c-a29a-6cd2a9ac8b26
-- title:
--   Residue: sum range le
-- statement:
--   The Residue construction uses the sum range le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ResidueLatticeCount/SumRangeLe.lean#L8-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ResidueLatticeCount/SumRangeLe.lean#L8-L25

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ResidueLatticeCount_HeckeLower
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ResidueLatticeCount_SumRangeLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.Residue
open MeasureTheory intervalIntegral

theorem PI.Residue.sum_range_le (s : ℝ) (hs : 1 < s) (N : ℕ) :
    ∑ i ∈ Finset.range N, ((1 : ℝ) + ((i + 1 : ℕ) : ℝ)) ^ (-s) ≤ 1 / (s - 1) := by sorry
