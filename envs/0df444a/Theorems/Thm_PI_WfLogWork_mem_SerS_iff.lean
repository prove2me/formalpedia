-- Prove2me | Theorems.Thm_PI_WfLogWork_mem_SerS_iff
-- name    : PI.WfLogWork.mem_SerS_iff
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T10:05:59.146876+00:00
-- url     : https://prove2.me/theorems/ac4bd573-6c65-4e10-b673-b09297525210
-- title:
--   Wf Log Work: mem Ser S iff
-- statement:
--   The Wf Log Work construction uses the mem Ser S iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WittLogarithm/FormalLogarithmHolds.lean#L11-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WittLogarithm/FormalLogarithmHolds.lean#L11-L22

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

theorem PI.WfLogWork.mem_SerS_iff {K : Type*} [CommRing K] (S : Subring K) (f : PowerSeries K) :
    (f : MvPowerSeries Unit K) ∈ SerS S Unit ↔ ∀ n, PowerSeries.coeff n f ∈ S := by sorry
