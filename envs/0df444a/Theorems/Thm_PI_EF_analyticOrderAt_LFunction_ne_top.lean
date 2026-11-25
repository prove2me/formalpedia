-- Prove2me | Theorems.Thm_PI_EF_analyticOrderAt_LFunction_ne_top
-- name    : PI.EF.analyticOrderAt_LFunction_ne_top
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:28:48.683629+00:00
-- url     : https://prove2.me/theorems/7777adf6-1285-4190-9f9a-8d71d02ac9b8
-- title:
--   EF: analytic Order At LFunction ne top
-- statement:
--   The EF construction uses the analytic Order At LFunction ne top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/GoodHeight.lean#L64-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/GoodHeight.lean#L64-L72

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

theorem PI.EF.analyticOrderAt_LFunction_ne_top {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {s : ℂ}
    (hs : s ≠ 1) : analyticOrderAt (LFunction χ) s ≠ ⊤ := by sorry
