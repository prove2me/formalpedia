-- Prove2me | Theorems.Thm_PI_EF_analyticOnNhd_LFunction
-- name    : PI.EF.analyticOnNhd_LFunction
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:23:04.458871+00:00
-- url     : https://prove2.me/theorems/2e1368eb-0746-4874-84ef-9dc527719f22
-- title:
--   EF: analytic On Nhd LFunction
-- statement:
--   The EF construction uses the analytic On Nhd LFunction property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/GoodHeight.lean#L54-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/GoodHeight.lean#L54-L58

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

theorem PI.EF.analyticOnNhd_LFunction {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) :
    AnalyticOnNhd ℂ (LFunction χ) {(1 : ℂ)}ᶜ := by sorry
