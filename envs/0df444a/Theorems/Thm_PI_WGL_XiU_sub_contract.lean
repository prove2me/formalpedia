-- Prove2me | Theorems.Thm_PI_WGL_XiU_sub_contract
-- name    : PI.WGL.XiU.sub_contract
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T05:45:51.677749+00:00
-- url     : https://prove2.me/theorems/3e821a2d-ce76-414d-ba90-09feb8ac842f
-- title:
--   Xi U: sub contract
-- statement:
--   The Xi U construction uses the sub contract property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/MultisetProdNormLeOne.lean#L37-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/MultisetProdNormLeOne.lean#L37-L61

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

theorem PI.WGL.XiU.sub_contract {N s : ℕ} (x : Matrix (Fin N) (Fin N) ℂ) (hx : x ∈ Matrix.unitaryGroup (Fin N) ℂ)
    (I J : Fin s → Fin N) (hI : Function.Injective I) (hJ : Function.Injective J) (v : Fin s → ℂ) :
    ∑ p, Complex.normSq (((Matrix.of fun p q => x (I p) (J q)) *ᵥ v) p) ≤ ∑ q, Complex.normSq (v q) := by sorry
