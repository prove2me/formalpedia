-- Prove2me | Theorems.Thm_PI_WGL_lm_isWH_map
-- name    : PI.WGL.lm_isWH_map
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T08:57:45.467887+00:00
-- url     : https://prove2.me/theorems/f1a47a15-6b36-5fe9-ba23-7550cce2402f
-- title:
--   WGL: lm is WH map
-- statement:
--   The WGL construction uses the lm is WH map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/LiftAsm.lean#L77-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/LiftAsm.lean#L77-L84

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

theorem PI.WGL.lm_isWH_map {σ M : Type*} [AddCommMonoid M] (w : σ → M) (f : MvPolynomial σ ℤ) (d : M)
    (hf : IsWeightedHomogeneous w f d) : IsWeightedHomogeneous w (map (Int.castRingHom ℂ) f) d := by sorry
