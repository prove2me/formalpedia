-- Prove2me | Theorems.Thm_PI_EF_PK_horiz_bound
-- name    : PI.EF.PK.horiz_bound
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:23:39.532068+00:00
-- url     : https://prove2.me/theorems/ef46bdad-d9c8-452b-a7fd-710fd7726432
-- title:
--   PK: horiz bound
-- statement:
--   The PK construction uses the horiz bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/PerronKernelA.lean#L20-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/PerronKernelA.lean#L20-L39

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

theorem PI.EF.PK.horiz_bound (l a b h : ℝ) (hl : l ≠ 0) (hh : h ≠ 0) (hab : a ≤ b) :
    ‖∫ x : ℝ in a..b, ker l ((x : ℂ) + h * I)‖ ≤
      (Real.exp (l * b) - Real.exp (l * a)) / l / |h| := by sorry
