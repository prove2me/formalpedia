-- Prove2me | Theorems.Thm_PI_EF_pTerm_le_far
-- name    : PI.EF.pTerm_le_far
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T05:29:03.068361+00:00
-- url     : https://prove2.me/theorems/603fc97c-2dbc-4339-837f-fa9261077f5e
-- title:
--   EF: p Term le far
-- statement:
--   The EF construction uses the p Term le far property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/PerronSumBound.lean#L159-L181
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/PerronSumBound.lean#L159-L181

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

theorem PI.EF.pTerm_le_far {u T : ℝ} (hu : 2 ≤ u) (hT : 0 < T) {n : ℕ} (hn : 0 < n)
    (h : (n : ℝ) ≤ u / 2 ∨ 2 * u ≤ n) :
    pTerm u T n ≤ (4 * Real.exp 1 * u / T) * logTerm (cLine u) n := by sorry
