-- Prove2me | Theorems.Thm_PI_WGL_XiU_det_sub_norm_le_one
-- name    : PI.WGL.XiU.det_sub_norm_le_one
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:45:24.347844+00:00
-- url     : https://prove2.me/theorems/8457e051-6b0d-5a4b-82ff-dff8cc03d080
-- title:
--   Xi U: det sub norm le one
-- statement:
--   The Xi U construction uses the det sub norm le one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/MultisetProdNormLeOne.lean#L72-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/MultisetProdNormLeOne.lean#L72-L102

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

theorem PI.WGL.XiU.det_sub_norm_le_one {N s : ℕ} (x : Matrix (Fin N) (Fin N) ℂ) (hx : x ∈ Matrix.unitaryGroup (Fin N) ℂ)
    (I J : Fin s → Fin N) (hI : Function.Injective I) (hJ : Function.Injective J) :
    ‖(Matrix.of fun p q => x (I p) (J q)).det‖ ≤ 1 := by sorry
