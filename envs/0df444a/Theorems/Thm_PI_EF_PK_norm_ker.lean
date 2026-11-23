-- Prove2me | Theorems.Thm_PI_EF_PK_norm_ker
-- name    : PI.EF.PK.norm_ker
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:22:33.228506+00:00
-- url     : https://prove2.me/theorems/858cc8a3-c58a-4d04-b4f0-379ba80a86f6
-- title:
--   PK: norm ker
-- statement:
--   The PK construction uses the norm ker property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/PerronKernelA.lean#L11-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/PerronKernelA.lean#L11-L13

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

theorem PI.EF.PK.norm_ker (l : ℝ) (s : ℂ) : ‖ker l s‖ = Real.exp (l * s.re) / ‖s‖ := by sorry
