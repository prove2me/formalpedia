-- Prove2me | Theorems.Thm_PI_WGL_lm_map_initMinor
-- name    : PI.WGL.lm_map_initMinor
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T08:55:28.406809+00:00
-- url     : https://prove2.me/theorems/c35ac08a-2fd4-597d-a5d4-fed55ca11096
-- title:
--   WGL: lm map init Minor
-- statement:
--   The WGL construction uses the lm map init Minor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/LiftAsm.lean#L110-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/LiftAsm.lean#L110-L116

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftDefs
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Wlocal
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftAsm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WGL
open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial

theorem PI.WGL.lm_map_initMinor {r m s : ℕ} (I : Fin s → Fin r) (hs : s ≤ m) :
    map (Int.castRingHom ℂ) (initMinor ℤ (n := m) I hs) = initMinor ℂ I hs := by sorry
