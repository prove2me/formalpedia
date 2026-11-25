-- Prove2me | Theorems.Thm_PI_FglChordFactor_Wk_formal_sub_first_zero
-- name    : PI.FglChordFactor.Wk.formal_sub_first_zero
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T09:43:49.958801+00:00
-- url     : https://prove2.me/theorems/b1e659ab-0cfc-5d48-b169-badf18bb54a9
-- title:
--   Wk: formal sub first zero
-- statement:
--   The Wk construction uses the formal sub first zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalGroupChords/SubstBivariateSeriesDifferencePair.lean#L151-L163
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalGroupChords/SubstBivariateSeriesDifferencePair.lean#L151-L163

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

theorem PI.FglChordFactor.Wk.formal_sub_first_zero {W : WeierstrassCurve ℂ_[p]} {wq ex : PowerSeries ℂ_[p]} (hW : IsWq W wq)
    (hexl : PowerSeries.subst (flog W wq) ex = PowerSeries.X) :
    MvPowerSeries.subst ![(0 : MvPowerSeries (Fin 2) ℂ_[p]), MvPowerSeries.X 1]
      (sub (flog W wq) ex (MvPowerSeries.X 0) (MvPowerSeries.X 1)) =
      PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) ℂ_[p]) (iW W wq) := by sorry
