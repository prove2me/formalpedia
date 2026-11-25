-- Prove2me | Theorems.Thm_PI_WGL_LTB_unl_perm
-- name    : PI.WGL.LTB.unl_perm
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T08:44:34.56367+00:00
-- url     : https://prove2.me/theorems/952fdb0f-8a6c-5bff-9559-3d31e1f6cef2
-- title:
--   LTB: unl perm
-- statement:
--   The LTB construction uses the unl perm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/LiftTupleB.lean#L29-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/LiftTupleB.lean#L29-L32

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftTupleM
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftTupleB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WGL PI.WGL.LTB
open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial PI.WGL.LTM

theorem PI.WGL.LTB.unl_perm {n N : ℕ} (h : n + 1 = N) {m : ℕ} (ρ : Fin m → Fin n) (hm : m ≤ N) (σ : Equiv.Perm (Fin m)) :
    unl h (ρ ∘ σ) hm = (Equiv.Perm.sign σ : ℤ) • unl h ρ hm := by sorry
