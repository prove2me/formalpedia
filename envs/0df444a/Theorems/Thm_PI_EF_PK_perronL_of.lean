-- Prove2me | Theorems.Thm_PI_EF_PK_perronL_of
-- name    : PI.EF.PK.perronL_of
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:27:49.891726+00:00
-- url     : https://prove2.me/theorems/8ad42d18-d2ea-4d6d-842b-72a0d89f1f89
-- title:
--   PK: perron L of
-- statement:
--   The PK construction uses the perron L of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/PerronLOf.lean#L23-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/PerronLOf.lean#L23-L60

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_PerronTruncOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_PerronLOf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.EF PI.EF.PK
open Complex MeasureTheory intervalIntegral Real ArithmeticFunction LSeries

theorem PI.EF.PK.perronL_of {C : ℝ} (hC : 0 ≤ C) (h : PerronTrunc C) : PerronL C := by sorry
