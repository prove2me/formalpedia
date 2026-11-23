-- Prove2me | Theorems.Thm_PI_FglChordFactor_Wk_serS_unit
-- name    : PI.FglChordFactor.Wk.serS_unit
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:59:56.131429+00:00
-- url     : https://prove2.me/theorems/cf43442d-05e9-45fe-b967-f6ffd098dcde
-- title:
--   Wk: ser S unit
-- statement:
--   The Wk construction uses the ser S unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalGroupChords/SubstPairSecondVariable.lean#L61-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalGroupChords/SubstPairSecondVariable.lean#L61-L65

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

theorem PI.FglChordFactor.Wk.serS_unit {S : Subring ℂ_[p]} {f : PowerSeries ℂ_[p]} (h : ∀ n, PowerSeries.coeff n f ∈ S) :
    (f : MvPowerSeries Unit ℂ_[p]) ∈ SerS S Unit := by sorry
