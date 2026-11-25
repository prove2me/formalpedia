-- Prove2me | Theorems.Thm_P2M_PI_FglChordFactor_Wk_derivative_flog__91738686ceb7
-- name    : P2M_PI_FglChordFactor_Wk_derivative_flog__91738686ceb7
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T09:39:57.450505+00:00
-- url     : https://prove2.me/theorems/6b4b0430-b3ce-4fc0-9a4d-b4c284cdd21e
-- title:
--   P2 M PI Fgl Chord Factor Wk derivative flog  91738686ceb7: P2 M PI Fgl Chord Factor Wk derivative flog  91738686ceb7
-- statement:
--   The P2 M PI Fgl Chord Factor Wk derivative flog  91738686ceb7 construction uses the P2 M PI Fgl Chord Factor Wk derivative flog  91738686ceb7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalGroupChords/DerivativeFlog.lean#L106-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalGroupChords/DerivativeFlog.lean#L106-L111

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_FglChordFactor
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_DXEqDerivative
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_DvCoeffMulEqZeroOfLtOrder
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_GlueHoldsVar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupChords_NormDeltaWc
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupChords_SubstPairSecondVariable
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupChords_DerivativeFlog
import Theorems.Thm_PI_AddIntG_Wk_inv_mem_SerS
import Theorems.Thm_PI_AddIntG_Wk_mem_SerS

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
open PI.AddIntG.Wk (SerS mem_SerS inv_mem_SerS)
variable {p : ℕ} [Fact p.Prime]

theorem P2M_PI_FglChordFactor_Wk_derivative_flog__91738686ceb7 (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]) :
    PowerSeries.derivative ℂ_[p] (flog W wq) = omegaW W wq := by sorry

alias «PI».«FglChordFactor».«Wk».«derivative_flog'» := P2M_PI_FglChordFactor_Wk_derivative_flog__91738686ceb7
