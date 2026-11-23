-- Prove2me | Theorems.Thm_PI_WGL_LTB_natW_last
-- name    : PI.WGL.LTB.natW_last
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:57:16.239803+00:00
-- url     : https://prove2.me/theorems/22f3af54-96b1-4998-a3e2-d5082a9c71bb
-- title:
--   LTB: nat W last
-- statement:
--   The LTB construction uses the nat W last property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/LiftTupleB.lean#L255-L256
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/LiftTupleB.lean#L255-L256

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

theorem PI.WGL.LTB.natW_last {n : ℕ} (sg : DomWeight n) (hn : 0 < n) : sg.natW ⟨n - 1, by omega⟩ = 0 := by sorry
