-- Prove2me | Theorems.Thm_PI_WGL_XiU_sum_comp_eq
-- name    : PI.WGL.XiU.sum_comp_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:57:49.775683+00:00
-- url     : https://prove2.me/theorems/bcb3ac08-0b10-426c-91d7-cc681e9ce4e5
-- title:
--   Xi U: sum comp eq
-- statement:
--   The Xi U construction uses the sum comp eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/MultisetProdNormLeOne.lean#L27-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/MultisetProdNormLeOne.lean#L27-L35

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_MultisetProdNormLeOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WGL PI.WGL.XiU
open Matrix

theorem PI.WGL.XiU.sum_comp_eq {N s : ℕ} {M : Type*} [AddCommMonoid M] (I : Fin s → Fin N) (hI : Function.Injective I)
    (f : Fin N → M) (hf : ∀ b, b ∉ Set.range I → f b = 0) : ∑ b, f b = ∑ p, f (I p) := by sorry
