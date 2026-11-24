-- Prove2me | Theorems.Thm_PI_QnCovHatW_swap4
-- name    : PI.QnCovHatW.swap4
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T15:03:58.135925+00:00
-- url     : https://prove2.me/theorems/e3743db6-d266-42e3-bd2e-078f159d30a6
-- title:
--   Qn Cov Hat W: swap4
-- statement:
--   The Qn Cov Hat W construction uses the swap4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CovariantHatDecomposition/SkipOneEqSuccAbove.lean#L32-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CovariantHatDecomposition/SkipOneEqSuccAbove.lean#L32-L40

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

theorem PI.QnCovHatW.swap4 {M : Type*} [AddCommMonoid M] {ι : Type*} [Fintype ι] (f : ι → ι → ι → ι → M) :
    ∑ i, ∑ j, ∑ i', ∑ j', f i j i' j' = ∑ i', ∑ j', ∑ i, ∑ j, f i j i' j' := by sorry
