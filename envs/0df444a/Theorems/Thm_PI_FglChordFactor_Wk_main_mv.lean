-- Prove2me | Theorems.Thm_PI_FglChordFactor_Wk_main_mv
-- name    : PI.FglChordFactor.Wk.main_mv
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T09:51:36.891214+00:00
-- url     : https://prove2.me/theorems/acd705bb-821c-4101-ba77-456446ae29b9
-- title:
--   Wk: main mv
-- statement:
--   The Wk construction uses the main mv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalGroupChords/FormalGroupChordFactor.lean#L13-L187
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalGroupChords/FormalGroupChordFactor.lean#L13-L187

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_FglChordFactor
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupChords_SubstBivariateSeriesDifferencePair
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupChords_FormalGroupChordFactor
import Theorems.Thm_PI_AddIntG_Wk_inv_mem_SerS
import Theorems.Thm_PI_AddIntG_Wk_mem_SerS
import Theorems.Thm_PI_AddIntG_Wk_mvsubst_mem_SerS
import Theorems.Thm_PI_AddIntG_Wk_subst_mem_SerS

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
open PI.AddIntG.Wk (SerS mem_SerS inv_mem_SerS mvsubst_mem_SerS subst_mem_SerS)

theorem PI.FglChordFactor.Wk.main_mv (p : ℕ) [Fact p.Prime] (W : WeierstrassCurve ℂ_[p]) (wq ex : PowerSeries ℂ_[p])
    (h1 : IsIntP W.a₁) (h2 : IsIntP W.a₂) (h3 : IsIntP W.a₃) (h4 : IsIntP W.a₄) (h6 : IsIntP W.a₆)
    (hW : IsWq W wq) (hex0 : PowerSeries.constantCoeff ex = 0)
    (hex : PowerSeries.subst ex (flog W wq) = PowerSeries.X)
    (hF : IntegralMv (add (flog W wq) ex (MvPowerSeries.X 0) (MvPowerSeries.X 1) : MvPowerSeries (Fin 2) ℂ_[p])) :
    ∃ n : MvPowerSeries (Fin 2) ℂ_[p], IntegralMv n ∧ MvPowerSeries.constantCoeff n = 1 ∧
      MvPowerSeries.X 0 ^ 2 * (PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) ℂ_[p]) wq)⁻¹ -
          MvPowerSeries.X 1 ^ 2 * (PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℂ_[p]) wq)⁻¹ =
        add (flog W wq) ex (MvPowerSeries.X 0) (MvPowerSeries.X 1) *
          sub (flog W wq) ex (MvPowerSeries.X 0) (MvPowerSeries.X 1) * n := by sorry
