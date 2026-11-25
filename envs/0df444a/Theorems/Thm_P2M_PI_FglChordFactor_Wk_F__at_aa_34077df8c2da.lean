-- Prove2me | Theorems.Thm_P2M_PI_FglChordFactor_Wk_F__at_aa_34077df8c2da
-- name    : P2M_PI_FglChordFactor_Wk_F__at_aa_34077df8c2da
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T09:43:41.063286+00:00
-- url     : https://prove2.me/theorems/48e3708e-66e8-4530-97b6-c9ac080fba7f
-- title:
--   P2 M PI Fgl Chord Factor Wk F  at aa 34077df8c2da: P2 M PI Fgl Chord Factor Wk F  at aa 34077df8c2da
-- statement:
--   The P2 M PI Fgl Chord Factor Wk F  at aa 34077df8c2da construction uses the P2 M PI Fgl Chord Factor Wk F  at aa 34077df8c2da property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalGroupChords/SubstBivariateSeriesDifferencePair.lean#L101-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalGroupChords/SubstBivariateSeriesDifferencePair.lean#L101-L106

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

theorem P2M_PI_FglChordFactor_Wk_F__at_aa_34077df8c2da {W : WeierstrassCurve ℂ_[p]} {wq ex : PowerSeries ℂ_[p]} (hex0 : PowerSeries.constantCoeff ex = 0) :
    MvPowerSeries.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℂ_[p]), MvPowerSeries.X 0]
      (sub (flog W wq) ex (MvPowerSeries.X 0) (MvPowerSeries.X 1)) = 0 := by sorry

alias «PI».«FglChordFactor».«Wk».«F'_at_aa» := P2M_PI_FglChordFactor_Wk_F__at_aa_34077df8c2da
