-- Prove2me | Theorems.Thm_PI_EF_pTerm_nonneg
-- name    : PI.EF.pTerm_nonneg
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T05:29:49.439668+00:00
-- url     : https://prove2.me/theorems/b2965e2e-8307-41cd-982a-f82fbd8632f8
-- title:
--   EF: p Term nonneg
-- statement:
--   The EF construction uses the p Term nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/PerronSumBound.lean#L149-L157
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/PerronSumBound.lean#L149-L157

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

theorem PI.EF.pTerm_nonneg {u T : ℝ} (hu : 0 < u) (hT : 0 < T) (n : ℕ) : 0 ≤ pTerm u T n := by sorry
