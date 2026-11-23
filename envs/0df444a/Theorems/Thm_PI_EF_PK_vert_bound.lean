-- Prove2me | Theorems.Thm_PI_EF_PK_vert_bound
-- name    : PI.EF.PK.vert_bound
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:22:41.554245+00:00
-- url     : https://prove2.me/theorems/dce8a38e-7996-4ec7-8faa-a2de57c5985f
-- title:
--   PK: vert bound
-- statement:
--   The PK construction uses the vert bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/PerronKernelA.lean#L41-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/PerronKernelA.lean#L41-L57

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

theorem PI.EF.PK.vert_bound (l x T : ℝ) (hx : x ≠ 0) (hT : 0 ≤ T) :
    ‖∫ t : ℝ in -T..T, ker l ((x : ℂ) + t * I)‖ ≤ Real.exp (l * x) / |x| * (2 * T) := by sorry
