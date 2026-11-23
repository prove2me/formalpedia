-- Prove2me | Theorems.Thm_PI_WGL_LTF_gmin_rowW
-- name    : PI.WGL.LTF.gmin_rowW
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:17:13.07075+00:00
-- url     : https://prove2.me/theorems/b77610d0-cab4-41c1-b3e3-659573fb74da
-- title:
--   LTF: gmin row W
-- statement:
--   The LTF construction uses the gmin row W property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/LiftTupleF.lean#L9-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/LiftTupleF.lean#L9-L24

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

theorem PI.WGL.LTF.gmin_rowW {r c m : ℕ} (ρ : Fin m → Fin r) (κ : Fin m → Fin c) :
    IsWeightedHomogeneous (rowW r c) (gmin ρ κ) (∑ p, (Pi.single (ρ p) 1 : Fin r → ℕ)) := by sorry
