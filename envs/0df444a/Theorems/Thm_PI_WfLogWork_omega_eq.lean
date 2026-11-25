-- Prove2me | Theorems.Thm_PI_WfLogWork_omega_eq
-- name    : PI.WfLogWork.omega_eq
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T10:05:53.070103+00:00
-- url     : https://prove2.me/theorems/332a38ee-5f64-52c0-91f6-13bfa9e7510c
-- title:
--   Wf Log Work: omega eq
-- statement:
--   The Wf Log Work construction uses the omega eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WittLogarithm/FormalLogarithmHolds.lean#L61-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WittLogarithm/FormalLogarithmHolds.lean#L61-L71

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WittLogarithm_CoefWfIff
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_DXEqDerivative
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_SubstMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WittLogarithm_FormalLogarithmHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WfLogWork
open PI.ExpIntWProof PI.AddIntG.Wk
variable {p : ℕ} [Fact p.Prime]

theorem PI.WfLogWork.omega_eq {W : WeierstrassCurve ℂ_[p]} {wq : PowerSeries ℂ_[p]} (hW : AddIntG.IsWq W wq) :
    AddIntG.omegaW W wq = (-Gv W (PowerSeries.X : PowerSeries ℂ_[p]) (wser wq))⁻¹ := by sorry
