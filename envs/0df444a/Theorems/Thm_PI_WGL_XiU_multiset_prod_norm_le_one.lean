-- Prove2me | Theorems.Thm_PI_WGL_XiU_multiset_prod_norm_le_one
-- name    : PI.WGL.XiU.multiset_prod_norm_le_one
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T05:45:38.071606+00:00
-- url     : https://prove2.me/theorems/79866ba0-cec6-4ec7-be1b-ce5a3e1ee1d7
-- title:
--   Xi U: multiset prod norm le one
-- statement:
--   The Xi U construction uses the multiset prod norm le one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/MultisetProdNormLeOne.lean#L63-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/MultisetProdNormLeOne.lean#L63-L70

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

theorem PI.WGL.XiU.multiset_prod_norm_le_one (m : Multiset ℂ) (h : ∀ μ ∈ m, ‖μ‖ ≤ 1) : ‖m.prod‖ ≤ 1 := by sorry
