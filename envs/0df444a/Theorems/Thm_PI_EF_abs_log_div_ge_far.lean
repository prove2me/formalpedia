-- Prove2me | Theorems.Thm_PI_EF_abs_log_div_ge_far
-- name    : PI.EF.abs_log_div_ge_far
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:28:54.453814+00:00
-- url     : https://prove2.me/theorems/336daefa-e47b-41bd-8f7b-aa23f5bdd12a
-- title:
--   EF: abs log div ge far
-- statement:
--   The EF construction uses the abs log div ge far property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/PerronSum.lean#L97-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/PerronSum.lean#L97-L110

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

theorem PI.EF.abs_log_div_ge_far {u x : ℝ} (hu : 0 < u) (hx : 0 < x) (h : x ≤ u / 2 ∨ 2 * u ≤ x) :
    Real.log 2 ≤ |Real.log (u / x)| := by sorry
