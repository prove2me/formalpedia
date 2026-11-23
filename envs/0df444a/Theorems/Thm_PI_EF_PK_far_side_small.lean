-- Prove2me | Theorems.Thm_PI_EF_PK_far_side_small
-- name    : PI.EF.PK.far_side_small
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:22:25.75426+00:00
-- url     : https://prove2.me/theorems/6246ceb0-d273-43ff-bded-27d094d0834e
-- title:
--   PK: far side small
-- statement:
--   The PK construction uses the far side small property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/PerronKernelA.lean#L64-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/PerronKernelA.lean#L64-L75

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

theorem PI.EF.PK.far_side_small (l x U T ε : ℝ) (hlx : l * x ≤ 0) (hxU : |x| = U) (hT : 0 < T) (hε : 0 < ε)
    (hU0 : 0 < U) (hUe : 2 * T / ε ≤ U) : Real.exp (l * x) / |x| * (2 * T) ≤ ε := by sorry
