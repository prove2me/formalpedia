-- Prove2me | Theorems.Thm_PI_WfLogWork_C_memS
-- name    : PI.WfLogWork.C_memS
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T10:05:32.226511+00:00
-- url     : https://prove2.me/theorems/962fdf50-a513-4a93-a968-f2840e3c1dcc
-- title:
--   Wf Log Work: C mem S
-- statement:
--   The Wf Log Work construction uses the C mem S property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WittLogarithm/FormalLogarithmHolds.lean#L26-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WittLogarithm/FormalLogarithmHolds.lean#L26-L31

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

theorem PI.WfLogWork.C_memS {S : Subring ℂ_[p]} {a : ℂ_[p]} (ha : a ∈ S) :
    ((algebraMap ℂ_[p] (PowerSeries ℂ_[p]) a : PowerSeries ℂ_[p]) : MvPowerSeries Unit ℂ_[p]) ∈ SerS S Unit := by sorry
