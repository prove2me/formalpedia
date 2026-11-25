-- Prove2me | Theorems.Thm_PI_QnCovHatW_det_sub_eq
-- name    : PI.QnCovHatW.det_sub_eq
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:38:12.186169+00:00
-- url     : https://prove2.me/theorems/7a3c2c62-1e8a-54d3-83dd-a9005130ff1f
-- title:
--   Qn Cov Hat W: det sub eq
-- statement:
--   The Qn Cov Hat W construction uses the det sub eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CovariantHatDecomposition/SkipOneEqSuccAbove.lean#L42-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CovariantHatDecomposition/SkipOneEqSuccAbove.lean#L42-L47

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

theorem PI.QnCovHatW.det_sub_eq {m : ℕ} (P : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) (i' i : Fin (m + 1)) :
    ∑ σ : Equiv.Perm (Fin m), ((Equiv.Perm.sign σ : ℤ) : ℂ) *
        ∏ k, P ((i'.succAbove ∘ σ) k) (i.succAbove k) =
      (P.submatrix i'.succAbove i.succAbove).det := by sorry
