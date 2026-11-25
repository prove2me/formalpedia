-- Prove2me | Theorems.Thm_PI_WGL_XiU_normSq_sum_eq
-- name    : PI.WGL.XiU.normSq_sum_eq
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T05:45:31.765579+00:00
-- url     : https://prove2.me/theorems/f9bac834-7fa9-4b3f-9f29-caed63214631
-- title:
--   Xi U: norm Sq sum eq
-- statement:
--   The Xi U construction uses the norm Sq sum eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/MultisetProdNormLeOne.lean#L9-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/MultisetProdNormLeOne.lean#L9-L13

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

theorem PI.WGL.XiU.normSq_sum_eq {N : ℕ} (u : Fin N → ℂ) :
    star u ⬝ᵥ u = ((∑ a, Complex.normSq (u a) : ℝ) : ℂ) := by sorry
