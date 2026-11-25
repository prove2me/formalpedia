-- Prove2me | Theorems.Thm_PI_WGL_lm_rowDiv_sub
-- name    : PI.WGL.lm_rowDiv_sub
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T05:47:08.876798+00:00
-- url     : https://prove2.me/theorems/b4879b68-c2c3-424b-8b25-448cea11f3d4
-- title:
--   WGL: lm row Div sub
-- statement:
--   The WGL construction uses the lm row Div sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/LiftAsm.lean#L57-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/LiftAsm.lean#L57-L60

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

theorem PI.WGL.lm_rowDiv_sub {R : Type*} [CommRing R] {r m : ℕ} (a b : Fin r) (k : ℕ)
    (f g : MvPolynomial (Fin r × Fin m) R) :
    rowDiv R a b k (f - g) = rowDiv R a b k f - rowDiv R a b k g := by sorry
