-- Prove2me | Theorems.Thm_PI_WfLogWork_coefWf_iff
-- name    : PI.WfLogWork.coefWf_iff
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T10:01:19.286487+00:00
-- url     : https://prove2.me/theorems/d9f7a4ce-321c-41cc-9332-e2ae11d8f876
-- title:
--   Wf Log Work: coef Wf iff
-- statement:
--   The Wf Log Work construction uses the coef Wf iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WittLogarithm/CoefWfIff.lean#L10-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WittLogarithm/CoefWfIff.lean#L10-L21

import Definitions.Def_Formalism_PeriodIntegrals_InvSerSub
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExponentialIntegrality_InvNatMemWf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WittLogarithm_CoefWfIff
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
open PI.ExpIntWProof

theorem PI.WfLogWork.coefWf_iff {p : ℕ} [Fact p.Prime] (f : PowerSeries ℂ_[p]) :
    CoefWf (f : MvPowerSeries Unit ℂ_[p]) ↔ ∀ n, PowerSeries.coeff n f ∈ Wf p := by sorry
