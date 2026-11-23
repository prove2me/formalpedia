-- Prove2me | Theorems.Thm_PI_EF_PK_gl_differentiable
-- name    : PI.EF.PK.gl_differentiable
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:22:47.337805+00:00
-- url     : https://prove2.me/theorems/24c13711-b177-4fbc-bf4f-01bb6e7096a5
-- title:
--   PK: gl differentiable
-- statement:
--   The PK construction uses the gl differentiable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/PerronKernelA.lean#L128-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/PerronKernelA.lean#L128-L133

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

theorem PI.EF.PK.gl_differentiable (l : ℝ) : Differentiable ℂ (gl l) := by sorry
