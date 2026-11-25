-- Prove2me | Theorems.Thm_PI_EF_analyticAt_LFunction
-- name    : PI.EF.analyticAt_LFunction
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T05:28:49.183789+00:00
-- url     : https://prove2.me/theorems/69112193-a14d-496f-9e17-4b23ebe130eb
-- title:
--   EF: analytic At LFunction
-- statement:
--   The EF construction uses the analytic At LFunction property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/GoodHeight.lean#L60-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/GoodHeight.lean#L60-L62

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_GoodHeightExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_GoodHeight
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
open DirichletCharacter

theorem PI.EF.analyticAt_LFunction {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : s ≠ 1) :
    AnalyticAt ℂ (LFunction χ) s := by sorry
