-- Prove2me | Theorems.Thm_PI_QnCovHatW_int_smul_eq
-- name    : PI.QnCovHatW.int_smul_eq
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T05:36:05.035909+00:00
-- url     : https://prove2.me/theorems/0602010c-8aac-5296-b5dc-2c9102c137f1
-- title:
--   Qn Cov Hat W: int smul eq
-- statement:
--   The Qn Cov Hat W construction uses the int smul eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CovariantHatDecomposition/SkipOneEqSuccAbove.lean#L28-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CovariantHatDecomposition/SkipOneEqSuccAbove.lean#L28-L30

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ContractionsCovariantIff
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_QuantumDetHighestWeightHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ShiftedGeneratorEqIteSmulAdd
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorCommutatorQuantumDet
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CovariantHatDecomposition_InjDecomp
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CovariantHatDecomposition_SkipOneEqSuccAbove
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Matrix Formalism.REAL Formalism.FourierDecayAlt.Q
open PI PI.QnCovHatW

theorem PI.QnCovHatW.int_smul_eq {A : Type} [Ring A] [Algebra ℂ A] (k : ℤ) (x : A) :
    ((k : ℂ)) • x = (k : A) * x := by sorry
