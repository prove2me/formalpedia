-- Prove2me | Theorems.Thm_P2M_PI_WGL_Adj_nf_sqAct_adj__7005aae57fcc
-- name    : P2M_PI_WGL_Adj_nf_sqAct_adj__7005aae57fcc
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T05:59:01.047656+00:00
-- url     : https://prove2.me/theorems/0e6702a7-83ea-490e-8ca9-3e501aca4ec7
-- title:
--   P2 M PI WGL Adj nf sq Act adj  7005aae57fcc: P2 M PI WGL Adj nf sq Act adj  7005aae57fcc
-- statement:
--   The P2 M PI WGL Adj nf sq Act adj  7005aae57fcc construction uses the P2 M PI WGL Adj nf sq Act adj  7005aae57fcc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/SqActMemNabla.lean#L84-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/SqActMemNabla.lean#L84-L86

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

theorem P2M_PI_WGL_Adj_nf_sqAct_adj__7005aae57fcc {N : ℕ} (lam : DomWeight N) (g : GL (Fin N) ℂ) (x y : MvPolynomial (Fin N × Fin N) ℂ) :
    normFock lam x (sqAct ℂ N lam g y) = normFock lam (sqAct ℂ N lam (gStar g) x) y := by sorry

alias «PI».«WGL».«Adj».«nf_sqAct_adj'» := P2M_PI_WGL_Adj_nf_sqAct_adj__7005aae57fcc
