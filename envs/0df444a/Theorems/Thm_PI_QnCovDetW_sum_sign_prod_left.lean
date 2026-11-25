-- Prove2me | Theorems.Thm_PI_QnCovDetW_sum_sign_prod_left
-- name    : PI.QnCovDetW.sum_sign_prod_left
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T08:18:06.274798+00:00
-- url     : https://prove2.me/theorems/047cb545-141a-4736-a3e6-44395ef7952d
-- title:
--   Qn Cov Det W: sum sign prod left
-- statement:
--   The Qn Cov Det W construction uses the sum sign prod left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CovariantDeterminantScaling/IntCastMulEqSmul.lean#L82-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CovariantDeterminantScaling/IntCastMulEqSmul.lean#L82-L86

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

theorem PI.QnCovDetW.sum_sign_prod_left {n : ℕ} (P : Matrix (Fin n) (Fin n) ℂ) :
    ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ k, P (σ k) k = P.det := by sorry
