-- Prove2me | Theorems.Thm_PI_QnCovHat2W_qminor_row_alt
-- name    : PI.QnCovHat2W.qminor_row_alt
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:37:58.374371+00:00
-- url     : https://prove2.me/theorems/22cf961a-51df-401b-a434-a97200675ae9
-- title:
--   Qn Cov Hat2 W: qminor row alt
-- statement:
--   The Qn Cov Hat2 W construction uses the qminor row alt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CovariantHatPairReindex/QnCovHat2OfLin.lean#L13-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CovariantHatPairReindex/QnCovHat2OfLin.lean#L13-L16

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CovariantHatPairReindex_SumSgnLProdCol
import Definitions.Def_Formalism_PeriodIntegrals_ContractionsCovariantIff
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_QuantumDetHighestWeightHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ShiftedGeneratorEqIteSmulAdd
import Definitions.Def_Formalism_FormalDegreeBessel_FinalIO
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CovariantHatPairReindex_QnCovHat2OfLin
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open PI PI.QnCovHat2W
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q

theorem PI.QnCovHat2W.qminor_row_alt {A : Type} [Ring A] [Algebra ℂ A] {n m : ℕ} (E : Fin n → Fin n → A) (u : ℂ)
    (x y : Fin m → Fin n) (π : Equiv.Perm (Fin m)) :
    qminor E (x ∘ π) y u = ((Equiv.Perm.sign π : ℤ) : ℂ) • qminor E x y u := by sorry
