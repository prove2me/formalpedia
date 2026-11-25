-- Prove2me | Theorems.Thm_P2M_PI_FglChordFactor_Wk_F__eq_d897049dae08
-- name    : P2M_PI_FglChordFactor_Wk_F__eq_d897049dae08
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T09:44:21.549225+00:00
-- url     : https://prove2.me/theorems/fd07d90e-e150-4288-baba-a44c951a8002
-- title:
--   P2 M PI Fgl Chord Factor Wk F  eq d897049dae08: P2 M PI Fgl Chord Factor Wk F  eq d897049dae08
-- statement:
--   The P2 M PI Fgl Chord Factor Wk F  eq d897049dae08 construction uses the P2 M PI Fgl Chord Factor Wk F  eq d897049dae08 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalGroupChords/SubstBivariateSeriesDifferencePair.lean#L108-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalGroupChords/SubstBivariateSeriesDifferencePair.lean#L108-L115

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

theorem P2M_PI_FglChordFactor_Wk_F__eq_d897049dae08 {W : WeierstrassCurve ℂ_[p]} {wq ex : PowerSeries ℂ_[p]} (hW : IsWq W wq) :
    sub (flog W wq) ex (MvPowerSeries.X 0) (MvPowerSeries.X 1) =
      MvPowerSeries.subst ![MvPowerSeries.X 0,
        PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) ℂ_[p]) (iW W wq)]
        (add (flog W wq) ex (MvPowerSeries.X 0) (MvPowerSeries.X 1)) := by sorry

alias «PI».«FglChordFactor».«Wk».«F'_eq» := P2M_PI_FglChordFactor_Wk_F__eq_d897049dae08
