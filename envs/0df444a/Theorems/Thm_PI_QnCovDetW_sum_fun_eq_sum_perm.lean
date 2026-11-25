-- Prove2me | Theorems.Thm_PI_QnCovDetW_sum_fun_eq_sum_perm
-- name    : PI.QnCovDetW.sum_fun_eq_sum_perm
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T08:26:47.970428+00:00
-- url     : https://prove2.me/theorems/9a1ba40b-b94d-4fd6-8efb-fb1eb3736181
-- title:
--   Qn Cov Det W: sum fun eq sum perm
-- statement:
--   The Qn Cov Det W construction uses the sum fun eq sum perm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CovariantDeterminantScaling/IntCastMulEqSmul.lean#L14-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CovariantDeterminantScaling/IntCastMulEqSmul.lean#L14-L29

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

theorem PI.QnCovDetW.sum_fun_eq_sum_perm {M : Type*} [AddCommMonoid M] {n : ℕ}
    (g : (Fin n → Fin n) → M) (hg : ∀ c, ¬ Function.Injective c → g c = 0) :
    ∑ c, g c = ∑ σ : Equiv.Perm (Fin n), g σ := by sorry
