-- Prove2me | Theorems.Thm_PI_EF_PK_line_bound_neg
-- name    : PI.EF.PK.line_bound_neg
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T05:28:36.323871+00:00
-- url     : https://prove2.me/theorems/b65480af-367a-4be2-8e02-b2b4b7ddc340
-- title:
--   PK: line bound neg
-- statement:
--   The PK construction uses the line bound neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/PerronKernelA.lean#L85-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/PerronKernelA.lean#L85-L124

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_GoodHeightExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_RectInv
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_PerronKernelA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.EF PI.EF.PK
open Complex MeasureTheory intervalIntegral Real

theorem PI.EF.PK.line_bound_neg (l c T : ℝ) (hl : l < 0) (hc : 0 < c) (hT : 0 < T) :
    ‖∫ t : ℝ in -T..T, ker l ((c : ℂ) + t * I)‖ ≤ 2 * (Real.exp (l * c) / (-l) / T) := by sorry
