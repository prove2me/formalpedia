-- Prove2me | Theorems.Thm_PI_EF_pTerm_le_near
-- name    : PI.EF.pTerm_le_near
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T05:29:18.111482+00:00
-- url     : https://prove2.me/theorems/4e4b653c-0707-4833-8de5-d5d2b0bd45b8
-- title:
--   EF: p Term le near
-- statement:
--   The EF construction uses the p Term le near property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/PerronSumBound.lean#L183-L210
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/PerronSumBound.lean#L183-L210

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

theorem PI.EF.pTerm_le_near {u T : ℝ} (hu : 2 ≤ u) (hT : 0 < T) {n : ℕ}
    (h1 : u / 2 < (n : ℝ)) (h2 : (n : ℝ) < 2 * u) :
    pTerm u T n ≤ 16 * Real.log u * nearB u T n := by sorry
