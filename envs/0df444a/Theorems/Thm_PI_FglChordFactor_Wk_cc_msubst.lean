-- Prove2me | Theorems.Thm_PI_FglChordFactor_Wk_cc_msubst
-- name    : PI.FglChordFactor.Wk.cc_msubst
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T09:44:13.543799+00:00
-- url     : https://prove2.me/theorems/1b6057bc-ab06-50c0-84dc-805aeccea513
-- title:
--   Wk: cc msubst
-- statement:
--   The Wk construction uses the cc msubst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalGroupChords/SubstBivariateSeriesDifferencePair.lean#L28-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalGroupChords/SubstBivariateSeriesDifferencePair.lean#L28-L42

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

theorem PI.FglChordFactor.Wk.cc_msubst {φ : Fin 2 → MvPowerSeries (Fin 2) ℂ_[p]} (hφ : MvPowerSeries.HasSubst φ)
    (hφ0 : ∀ i, MvPowerSeries.constantCoeff (φ i) = 0) (H : MvPowerSeries (Fin 2) ℂ_[p]) :
    MvPowerSeries.constantCoeff (MvPowerSeries.subst φ H) = MvPowerSeries.constantCoeff H := by sorry
