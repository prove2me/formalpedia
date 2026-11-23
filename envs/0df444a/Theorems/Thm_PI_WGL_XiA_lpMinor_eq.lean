-- Prove2me | Theorems.Thm_PI_WGL_XiA_lpMinor_eq
-- name    : PI.WGL.XiA.lpMinor_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:01:00.391828+00:00
-- url     : https://prove2.me/theorems/6309105e-ba22-4130-b766-66e11fa7042f
-- title:
--   Xi A: lp Minor eq
-- statement:
--   The Xi A construction uses the lp Minor eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/RowsZStrictMono.lean#L71-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/RowsZStrictMono.lean#L71-L72

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_ZScalarVanish
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_MultisetProdNormLeOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_RowsZStrictMono
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WGL PI.WGL.XiA
open Formalism.BasicNotions MvPolynomial

theorem PI.WGL.XiA.lpMinor_eq {N : ℕ} (s : ℕ) (hr : s ≤ N) (hn : s ≤ N) :
    Formalism.GradedWeylDivisibility.lpMinor ℂ (r := N) (n := N) s hr hn = Formalism.GradedWeylDivisibility.initMinor ℂ (n := N) (Fin.castLE hr) hn := by sorry
