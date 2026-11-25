-- Prove2me | Theorems.Thm_PI_WGL_LTE_lam_natW_val
-- name    : PI.WGL.LTE.lam_natW_val
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T05:45:29.238602+00:00
-- url     : https://prove2.me/theorems/fbfbd5fa-ef53-4493-8f9c-06ddf94b6ac2
-- title:
--   LTE: lam nat W val
-- statement:
--   The LTE construction uses the lam nat W val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/LiftTupleE.lean#L92-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/LiftTupleE.lean#L92-L103

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftTupleD
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftTupleE
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WGL PI.WGL.LTE
open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial PI.WGL.LTA PI.WGL.LTM PI.WGL.LTC PI.WGL.LTD

theorem PI.WGL.LTE.lam_natW_val {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (t : ℕ) (ht : t < N) :
    ((lam.natW ⟨t, ht⟩ : ℕ) : ℤ) = lam.w ⟨t, ht⟩ - lam.w ⟨n, by omega⟩ := by sorry
