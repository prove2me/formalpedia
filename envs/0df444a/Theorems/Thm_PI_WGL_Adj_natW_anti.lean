-- Prove2me | Theorems.Thm_PI_WGL_Adj_natW_anti
-- name    : PI.WGL.Adj.natW_anti
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T05:46:44.352803+00:00
-- url     : https://prove2.me/theorems/bc1fef27-15de-4e6e-ad64-703918913c6d
-- title:
--   Adj: nat W anti
-- statement:
--   The Adj construction uses the nat W anti property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/SqActMemNabla.lean#L88-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/SqActMemNabla.lean#L88-L91

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

theorem PI.WGL.Adj.natW_anti {N : ℕ} (lam : DomWeight N) : Antitone lam.natW := by sorry
