-- Prove2me | Theorems.Thm_PI_QnCovHatW_scal
-- name    : PI.QnCovHatW.scal
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T15:03:48.54804+00:00
-- url     : https://prove2.me/theorems/10e634e6-3484-46a9-beab-6480476de613
-- title:
--   Qn Cov Hat W: scal
-- statement:
--   The Qn Cov Hat W construction uses the scal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CovariantHatDecomposition/SkipOneEqSuccAbove.lean#L56-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CovariantHatDecomposition/SkipOneEqSuccAbove.lean#L56-L106

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

theorem PI.QnCovHatW.scal {m : ℕ} (P Q : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) (hPQ : P * Q = 1)
    (a β : Fin (m + 1) → ℂ) (i' j' : Fin (m + 1)) :
    ∑ i : Fin (m + 1), ∑ j : Fin (m + 1),
        ((-1 : ℂ) ^ ((i : ℕ) + (j : ℕ)) * (β ᵥ* P) i * (Q *ᵥ a) j) *
          ((P.submatrix i'.succAbove i.succAbove).det * (Q.submatrix j.succAbove j'.succAbove).det) =
      (-1 : ℂ) ^ ((i' : ℕ) + (j' : ℕ)) * β i' * a j' := by sorry
