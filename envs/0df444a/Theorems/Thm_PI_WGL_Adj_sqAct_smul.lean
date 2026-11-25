-- Prove2me | Theorems.Thm_PI_WGL_Adj_sqAct_smul
-- name    : PI.WGL.Adj.sqAct_smul
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T05:49:10.503732+00:00
-- url     : https://prove2.me/theorems/92450d6a-001b-436e-b6e8-023fad01c3e0
-- title:
--   Adj: sq Act smul
-- statement:
--   The Adj construction uses the sq Act smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/SqActMemNabla.lean#L65-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/SqActMemNabla.lean#L65-L68

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_AdjBase
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_SqActMemNabla
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WGL PI.WGL.Adj
open Formalism.BasicNotions MvPolynomial

theorem PI.WGL.Adj.sqAct_smul {N : ℕ} (lam : DomWeight N) (g : GL (Fin N) ℂ) (c : ℂ) (f : MvPolynomial (Fin N × Fin N) ℂ) :
    sqAct ℂ N lam g (c • f) = c • sqAct ℂ N lam g f := by sorry
