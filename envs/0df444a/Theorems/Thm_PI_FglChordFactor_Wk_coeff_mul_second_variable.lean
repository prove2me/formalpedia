-- Prove2me | Theorems.Thm_PI_FglChordFactor_Wk_coeff_mul_second_variable
-- name    : PI.FglChordFactor.Wk.coeff_mul_second_variable
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T05:29:19.818881+00:00
-- url     : https://prove2.me/theorems/7795cc41-4726-405a-af8a-63fa54a91f4e
-- title:
--   Wk: coeff mul second variable
-- statement:
--   The Wk construction uses the coeff mul second variable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalGroupChords/SubstPairSecondVariable.lean#L72-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalGroupChords/SubstPairSecondVariable.lean#L72-L77

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_FglChordFactor
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_SubstMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_FormalGroupLawExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupChords_SubstPairSecondVariable
import Theorems.Thm_PI_AddIntG_Wk_mem_SerS
import Theorems.Thm_PI_AddIntG_Wk_mvsubst_mem_SerS
import Theorems.Thm_PI_AddIntG_Wk_subst_mem_SerS
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
open PI.AddIntG.Wk (SerS mem_SerS mvsubst_mem_SerS subst_mem_SerS subst_psubst)
variable {p : ℕ} [Fact p.Prime]

theorem PI.FglChordFactor.Wk.coeff_mul_second_variable (f : MvPowerSeries (Fin 2) ℂ_[p]) (e : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff e (f * MvPowerSeries.X 1) =
      if 1 ≤ e 1 then MvPowerSeries.coeff (e - Finsupp.single 1 1) f else 0 := by sorry
