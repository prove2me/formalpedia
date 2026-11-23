-- Prove2me | Theorems.Thm_PI_WGL_LTB_initMinor_perm
-- name    : PI.WGL.LTB.initMinor_perm
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T03:08:33.503698+00:00
-- url     : https://prove2.me/theorems/e94ebeb5-390e-40f5-85eb-1904d03845cc
-- title:
--   LTB: init Minor perm
-- statement:
--   The LTB construction uses the init Minor perm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/LiftTupleB.lean#L9-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/LiftTupleB.lean#L9-L15

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

theorem PI.WGL.LTB.initMinor_perm {R : Type*} [CommRing R] {r m s : ℕ} (I : Fin s → Fin r) (hs : s ≤ m)
    (σ : Equiv.Perm (Fin s)) :
    initMinor R (n := m) (I ∘ σ) hs = (Equiv.Perm.sign σ : ℤ) • initMinor R (n := m) I hs := by sorry
