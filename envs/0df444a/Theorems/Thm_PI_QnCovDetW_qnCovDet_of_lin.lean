-- Prove2me | Theorems.Thm_PI_QnCovDetW_qnCovDet_of_lin
-- name    : PI.QnCovDetW.qnCovDet_of_lin
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T08:18:04.122467+00:00
-- url     : https://prove2.me/theorems/856daee9-d5a4-5dc2-91da-3fd979a0e056
-- title:
--   Qn Cov Det W: qn Cov Det of lin
-- statement:
--   The Qn Cov Det W construction uses the qn Cov Det of lin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CovariantDeterminantScaling/IntCastMulEqSmul.lean#L94-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CovariantDeterminantScaling/IntCastMulEqSmul.lean#L94-L127

import Definitions.Def_Formalism_PeriodIntegrals_ContractionsCovariantIff
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_QuantumDetHighestWeightHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ShiftedGeneratorEqIteSmulAdd
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorCommutatorQuantumDet
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CovariantDeterminantScaling_IntCastMulEqSmul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
noncomputable section
open PI PI.QnCovDetW
open Formalism.REAL Formalism.FourierDecayAlt.Q

theorem PI.QnCovDetW.qnCovDet_of_lin (h : PI.QnCovLin) : PI.QnCovDet := by sorry
