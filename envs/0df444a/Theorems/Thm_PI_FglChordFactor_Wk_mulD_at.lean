-- Prove2me | Theorems.Thm_PI_FglChordFactor_Wk_mulD_at
-- name    : PI.FglChordFactor.Wk.mulD_at
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T09:43:03.688651+00:00
-- url     : https://prove2.me/theorems/d95fa8c3-ffce-594f-9985-c378942cfb28
-- title:
--   Wk: mul D at
-- statement:
--   The Wk construction uses the mul D at property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalGroupChords/SubstBivariateSeriesDifferencePair.lean#L74-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalGroupChords/SubstBivariateSeriesDifferencePair.lean#L74-L78

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_FglChordFactor
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupChords_DerivativeFlog
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupChords_SubstBivariateSeriesDifferencePair
import Theorems.Thm_PI_AddIntG_Wk_mem_SerS
import Theorems.Thm_PI_AddIntG_Wk_subst_psubst

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Classical
open PI PI.FglChordFactor PI.FglChordFactor.Wk
open PI.AddIntG.Wk (SerS mem_SerS subst_psubst)
variable {p : ℕ} [Fact p.Prime]

theorem PI.FglChordFactor.Wk.mulD_at (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]) {u : MvPowerSeries (Fin 2) ℂ_[p]}
    (hu : PowerSeries.HasSubst u) :
    PowerSeries.subst u (iW W wq) * PowerSeries.subst u (Dser W wq) = -u := by sorry
