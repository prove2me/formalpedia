-- Prove2me | Theorems.Thm_PI_QnCovHatW_skip_one_eq_succAbove
-- name    : PI.QnCovHatW.skip_one_eq_succAbove
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T15:03:49.4348+00:00
-- url     : https://prove2.me/theorems/2a788efb-9d2e-4c0b-82ed-23de0b323a09
-- title:
--   Qn Cov Hat W: skip one eq succ Above
-- statement:
--   The Qn Cov Hat W construction uses the skip one eq succ Above property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CovariantHatDecomposition/SkipOneEqSuccAbove.lean#L12-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CovariantHatDecomposition/SkipOneEqSuccAbove.lean#L12-L19

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

theorem PI.QnCovHatW.skip_one_eq_succAbove {m : ℕ} (i : Fin (m + 1)) (j : Fin m) : skip1 (t := m + 1) i j = i.succAbove j := by sorry
