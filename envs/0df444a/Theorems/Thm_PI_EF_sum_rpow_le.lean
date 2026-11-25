-- Prove2me | Theorems.Thm_PI_EF_sum_rpow_le
-- name    : PI.EF.sum_rpow_le
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T05:29:23.486636+00:00
-- url     : https://prove2.me/theorems/4b72e034-37e0-4198-b3d1-3327322799f0
-- title:
--   EF: sum rpow le
-- statement:
--   The EF construction uses the sum rpow le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/PerronSum.lean#L10-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/PerronSum.lean#L10-L36

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

theorem PI.EF.sum_rpow_le {ε : ℝ} (hε : 0 < ε) (K : ℕ) :
    ∑ i ∈ range K, ((i : ℝ) + 2) ^ (-(1 + ε)) ≤ 1 / ε := by sorry
