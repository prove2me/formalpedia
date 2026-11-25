-- Prove2me | Theorems.Thm_PI_EF_pTerm_le
-- name    : PI.EF.pTerm_le
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T05:29:31.337798+00:00
-- url     : https://prove2.me/theorems/de42a0cb-9a59-4aa3-9ea8-25fb777a9eeb
-- title:
--   EF: p Term le
-- statement:
--   The EF construction uses the p Term le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/PerronSumBound.lean#L212-L238
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/PerronSumBound.lean#L212-L238

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

theorem PI.EF.pTerm_le {u T : ℝ} (hu : 2 ≤ u) (hT : 0 < T) (n : ℕ) :
    pTerm u T n ≤ (4 * Real.exp 1 * u / T) * logTerm (cLine u) n +
      16 * Real.log u * (if n < ⌊u⌋₊ + (⌊u⌋₊ + 2) then nearB u T n else 0) := by sorry
