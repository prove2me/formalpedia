-- Prove2me | Theorems.Thm_PI_WGL_XiU_sum_comp_le
-- name    : PI.WGL.XiU.sum_comp_le
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:45:52.073831+00:00
-- url     : https://prove2.me/theorems/87f66be2-0df3-448b-940c-cf510b3d64d6
-- title:
--   Xi U: sum comp le
-- statement:
--   The Xi U construction uses the sum comp le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/MultisetProdNormLeOne.lean#L22-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/MultisetProdNormLeOne.lean#L22-L25

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

theorem PI.WGL.XiU.sum_comp_le {N s : ℕ} (I : Fin s → Fin N) (hI : Function.Injective I) (f : Fin N → ℝ)
    (hf : ∀ a, 0 ≤ f a) : ∑ p, f (I p) ≤ ∑ a, f a := by sorry
