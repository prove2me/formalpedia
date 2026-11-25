-- Prove2me | Theorems.Thm_PI_WGL_XiU_normSq_sum_mulVec
-- name    : PI.WGL.XiU.normSq_sum_mulVec
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:45:34.153212+00:00
-- url     : https://prove2.me/theorems/20fd799c-0d7a-5b76-aa69-04b662f6d093
-- title:
--   Xi U: norm Sq sum mul Vec
-- statement:
--   The Xi U construction uses the norm Sq sum mul Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/MultisetProdNormLeOne.lean#L15-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/MultisetProdNormLeOne.lean#L15-L20

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

theorem PI.WGL.XiU.normSq_sum_mulVec {N : ℕ} (x : Matrix (Fin N) (Fin N) ℂ) (hx : x ∈ Matrix.unitaryGroup (Fin N) ℂ)
    (w : Fin N → ℂ) : ∑ a, Complex.normSq ((x *ᵥ w) a) = ∑ b, Complex.normSq (w b) := by sorry
