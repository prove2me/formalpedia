-- Prove2me | Theorems.Thm_PI_WGL_EqvWt_weight_lastW
-- name    : PI.WGL.EqvWt.weight_lastW
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T05:47:40.86506+00:00
-- url     : https://prove2.me/theorems/b09a77d3-d9c7-4e96-ad39-ad395a1583eb
-- title:
--   Eqv Wt: weight last W
-- statement:
--   The Eqv Wt construction uses the weight last W property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/LiftEqvWt.lean#L87-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/LiftEqvWt.lean#L87-L98

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftEqvWt
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
open PI.WGL.EqvWt

theorem PI.WGL.EqvWt.weight_lastW {n : ℕ} (m : Fin (n + 1) × Fin (n + 1) →₀ ℕ) :
    Finsupp.weight (lastW (n + 1)) m = rowDeg m (Fin.last n) := by sorry
