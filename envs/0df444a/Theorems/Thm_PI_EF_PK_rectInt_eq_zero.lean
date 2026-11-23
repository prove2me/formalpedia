-- Prove2me | Theorems.Thm_PI_EF_PK_rectInt_eq_zero
-- name    : PI.EF.PK.rectInt_eq_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:22:49.622704+00:00
-- url     : https://prove2.me/theorems/683fef43-5c61-494e-9f53-087ffe9bd8af
-- title:
--   PK: rect Int eq zero
-- statement:
--   The PK construction uses the rect Int eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/PerronKernelA.lean#L59-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/PerronKernelA.lean#L59-L62

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

theorem PI.EF.PK.rectInt_eq_zero (f : ℂ → ℂ) (a b c d : ℝ)
    (H : DifferentiableOn ℂ f (Set.uIcc a b ×ℂ Set.uIcc c d)) : rectInt f a b c d = 0 := by sorry
