-- Prove2me | Theorems.Thm_PI_WGL_Adj_gStar_gStar
-- name    : PI.WGL.Adj.gStar_gStar
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T06:00:20.069695+00:00
-- url     : https://prove2.me/theorems/8a0ee6e4-1d57-5d05-82e5-8b8a60d003ca
-- title:
--   Adj: g Star g Star
-- statement:
--   The Adj construction uses the g Star g Star property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/SqActMemNabla.lean#L19-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/SqActMemNabla.lean#L19-L20

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

theorem PI.WGL.Adj.gStar_gStar {N : ℕ} (g : GL (Fin N) ℂ) : gStar (gStar g) = g := by sorry
