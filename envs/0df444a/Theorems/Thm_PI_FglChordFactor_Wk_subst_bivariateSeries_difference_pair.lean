-- Prove2me | Theorems.Thm_PI_FglChordFactor_Wk_subst_bivariateSeries_difference_pair
-- name    : PI.FglChordFactor.Wk.subst_bivariateSeries_difference_pair
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T09:43:39.361495+00:00
-- url     : https://prove2.me/theorems/26387d14-6f2b-469d-bb53-e78b37949bd6
-- title:
--   Wk: subst bivariate Series difference pair
-- statement:
--   The Wk construction uses the subst bivariate Series difference pair property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalGroupChords/SubstBivariateSeriesDifferencePair.lean#L56-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalGroupChords/SubstBivariateSeriesDifferencePair.lean#L56-L66

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

theorem PI.FglChordFactor.Wk.subst_bivariateSeries_difference_pair {l ex : PowerSeries ℂ_[p]} (hl0 : PowerSeries.constantCoeff l = 0)
    {u v : MvPowerSeries (Fin 2) ℂ_[p]} (hs : MvPowerSeries.HasSubst ![u, v]) :
    MvPowerSeries.subst ![u, v] (sub l ex (MvPowerSeries.X 0) (MvPowerSeries.X 1)) = sub l ex u v := by sorry
