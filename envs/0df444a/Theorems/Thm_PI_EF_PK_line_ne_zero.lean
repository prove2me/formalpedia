-- Prove2me | Theorems.Thm_PI_EF_PK_line_ne_zero
-- name    : PI.EF.PK.line_ne_zero
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:27:43.205914+00:00
-- url     : https://prove2.me/theorems/dd417a85-daad-4551-97bb-217a6bbaf0cb
-- title:
--   PK: line ne zero
-- statement:
--   The PK construction uses the line ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/PerronKernelB.lean#L31-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/PerronKernelB.lean#L31-L35

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_PerronKernelA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_PerronKernelB
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

theorem PI.EF.PK.line_ne_zero (c : ℝ) (hc : 0 < c) (t : ℝ) : (c : ℂ) + t * I ≠ 0 := by sorry
