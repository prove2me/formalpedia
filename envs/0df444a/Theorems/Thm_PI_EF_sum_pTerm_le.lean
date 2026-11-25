-- Prove2me | Theorems.Thm_PI_EF_sum_pTerm_le
-- name    : PI.EF.sum_pTerm_le
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T05:29:50.10618+00:00
-- url     : https://prove2.me/theorems/469ac382-a9ff-475c-87d9-345f9231fdb4
-- title:
--   EF: sum p Term le
-- statement:
--   The EF construction uses the sum p Term le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/PerronSumBound.lean#L240-L293
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/PerronSumBound.lean#L240-L293

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

theorem PI.EF.sum_pTerm_le {u T : ℝ} (hu : 2 ≤ u) (hT : 2 ≤ T) (K : ℕ) :
    ∑ n ∈ range K, pTerm u T n ≤ 500 * (u * Real.log u ^ 2 / T + Real.log u) := by sorry
