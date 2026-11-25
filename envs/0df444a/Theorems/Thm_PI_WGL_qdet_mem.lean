-- Prove2me | Theorems.Thm_PI_WGL_qdet_mem
-- name    : PI.WGL.qdet_mem
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T05:59:53.545971+00:00
-- url     : https://prove2.me/theorems/5bf232c6-c16d-5a1c-bb1e-1d640e161fbc
-- title:
--   WGL: qdet mem
-- statement:
--   The WGL construction uses the qdet mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/CapelliZ.lean#L94-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/CapelliZ.lean#L94-L104

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_CapelliShift
import Definitions.Def_Lemmata_GeneralBFactRight_Imports
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_CapelliZ
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

theorem PI.WGL.qdet_mem {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (w : ℤ) :
    Formalism.REAL.qdet (capE h lam) (w : ℂ) ∈ presRing lam := by sorry
