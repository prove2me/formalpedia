-- Prove2me | Theorems.Thm_PI_WGL_LTF_ite_pow_rowW
-- name    : PI.WGL.LTF.ite_pow_rowW
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T05:48:51.377447+00:00
-- url     : https://prove2.me/theorems/931c4897-1857-42bd-83ff-8097af05c903
-- title:
--   LTF: ite pow row W
-- statement:
--   The LTF construction uses the ite pow row W property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/LiftTupleF.lean#L40-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/LiftTupleF.lean#L40-L45

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftTupleE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftTupleF
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WGL PI.WGL.LTF
open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial PI.WGL.LTA PI.WGL.LTM PI.WGL.LTC PI.WGL.LTD PI.WGL.LTE

theorem PI.WGL.LTF.ite_pow_rowW {N : ℕ} (c : Prop) [Decidable c] (f : MvPolynomial (Fin N × Fin N) ℤ) (w : Fin N → ℕ)
    (hf : IsWeightedHomogeneous (rowW N N) f w) (e : ℕ) :
    IsWeightedHomogeneous (rowW N N) (if c then f ^ e else 1) ((if c then e else 0) • w) := by sorry
