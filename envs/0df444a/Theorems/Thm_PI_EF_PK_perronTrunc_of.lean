-- Prove2me | Theorems.Thm_PI_EF_PK_perronTrunc_of
-- name    : PI.EF.PK.perronTrunc_of
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:27:53.538134+00:00
-- url     : https://prove2.me/theorems/f9ce20df-d29f-4551-b331-718a837dedc7
-- title:
--   PK: perron Trunc of
-- statement:
--   The PK construction uses the perron Trunc of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/PerronTruncOf.lean#L32-L158
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/PerronTruncOf.lean#L32-L158

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_GoodHeightExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_PerronTruncOf
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

theorem PI.EF.PK.perronTrunc_of {C : ℝ} (hK : PerronKernel) (hS : PerronSumBound C) : PerronTrunc C := by sorry
