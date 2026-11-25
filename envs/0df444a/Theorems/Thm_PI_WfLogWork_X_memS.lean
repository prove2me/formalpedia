-- Prove2me | Theorems.Thm_PI_WfLogWork_X_memS
-- name    : PI.WfLogWork.X_memS
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T10:06:10.14808+00:00
-- url     : https://prove2.me/theorems/d3c62be9-3b03-41d8-aa41-4a29251638b9
-- title:
--   Wf Log Work: X mem S
-- statement:
--   The Wf Log Work construction uses the X mem S property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WittLogarithm/FormalLogarithmHolds.lean#L33-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WittLogarithm/FormalLogarithmHolds.lean#L33-L38

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

theorem PI.WfLogWork.X_memS (S : Subring ℂ_[p]) :
    ((PowerSeries.X : PowerSeries ℂ_[p]) : MvPowerSeries Unit ℂ_[p]) ∈ SerS S Unit := by sorry
