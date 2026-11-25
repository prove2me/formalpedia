-- Prove2me | Theorems.Thm_PI_EF_log_window_le
-- name    : PI.EF.log_window_le
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T05:29:45.448285+00:00
-- url     : https://prove2.me/theorems/1ffb3f6b-b7bf-5612-b022-ce60f9d248df
-- title:
--   EF: log window le
-- statement:
--   The EF construction uses the log window le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/LogWindowLe.lean#L12-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/LogWindowLe.lean#L12-L28

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_NormSubCtrSq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_ExplicitFormulaFromGluing
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_LogWindowLe
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
open Complex Metric Filter Topology Set DirichletCharacter
variable {N : ℕ} [NeZero N]

theorem PI.EF.log_window_le (N : ℕ) [NeZero N] {t u : ℝ} (hu : |u| ≤ |t| + 2) :
    Real.log (N * (|u| + 2)) ≤ 2 * LL N t := by sorry
