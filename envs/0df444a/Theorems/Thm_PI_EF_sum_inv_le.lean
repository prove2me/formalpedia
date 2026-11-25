-- Prove2me | Theorems.Thm_PI_EF_sum_inv_le
-- name    : PI.EF.sum_inv_le
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T05:30:06.020539+00:00
-- url     : https://prove2.me/theorems/2082617d-768b-4991-a55a-2e3c3c491f7b
-- title:
--   EF: sum inv le
-- statement:
--   The EF construction uses the sum inv le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/PerronSumBound.lean#L26-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/PerronSumBound.lean#L26-L33

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_PerronSum
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_PerronSumBound
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

theorem PI.EF.sum_inv_le (n : ℕ) : ∑ j ∈ range n, 1 / ((j : ℝ) + 1) ≤ 1 + Real.log n := by sorry
