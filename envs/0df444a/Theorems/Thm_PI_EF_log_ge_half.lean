-- Prove2me | Theorems.Thm_PI_EF_log_ge_half
-- name    : PI.EF.log_ge_half
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:24:09.497185+00:00
-- url     : https://prove2.me/theorems/c57fc34a-1ca6-4f79-9f8e-838609cccb5e
-- title:
--   EF: log ge half
-- statement:
--   The EF construction uses the log ge half property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/PerronSum.lean#L112-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/PerronSum.lean#L112-L115

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

theorem PI.EF.log_ge_half {u : ℝ} (hu : 2 ≤ u) : 1 / 2 ≤ Real.log u := by sorry
