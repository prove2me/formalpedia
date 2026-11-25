-- Prove2me | Theorems.Thm_P2M_PI_FglChordFactor_Wk_wq_const__1de777e7fcd2
-- name    : P2M_PI_FglChordFactor_Wk_wq_const__1de777e7fcd2
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T09:40:08.378803+00:00
-- url     : https://prove2.me/theorems/71683cb9-8453-4c1b-b13c-4a108d82e6e6
-- title:
--   P2 M PI Fgl Chord Factor Wk wq const  1de777e7fcd2: P2 M PI Fgl Chord Factor Wk wq const  1de777e7fcd2
-- statement:
--   The P2 M PI Fgl Chord Factor Wk wq const  1de777e7fcd2 construction uses the P2 M PI Fgl Chord Factor Wk wq const  1de777e7fcd2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalGroupChords/DerivativeFlog.lean#L27-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalGroupChords/DerivativeFlog.lean#L27-L33

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

theorem P2M_PI_FglChordFactor_Wk_wq_const__1de777e7fcd2 {W : WeierstrassCurve ℂ_[p]} {wq : PowerSeries ℂ_[p]} (h : IsWq W wq) :
    PowerSeries.constantCoeff wq = 1 := by sorry

alias «PI».«FglChordFactor».«Wk».«wq_const'» := P2M_PI_FglChordFactor_Wk_wq_const__1de777e7fcd2
