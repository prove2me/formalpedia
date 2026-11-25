-- Prove2me | Theorems.Thm_P2M_PI_QnCovHatW_det_sub_eq__8094bc80bf43
-- name    : P2M_PI_QnCovHatW_det_sub_eq__8094bc80bf43
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T04:59:09.066342+00:00
-- url     : https://prove2.me/theorems/51d5ebb0-5458-47d8-9823-0be0a3c935a8
-- title:
--   P2 M PI Qn Cov Hat W det sub eq  8094bc80bf43: P2 M PI Qn Cov Hat W det sub eq  8094bc80bf43
-- statement:
--   The P2 M PI Qn Cov Hat W det sub eq  8094bc80bf43 construction uses the P2 M PI Qn Cov Hat W det sub eq  8094bc80bf43 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CovariantHatDecomposition/SkipOneEqSuccAbove.lean#L49-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CovariantHatDecomposition/SkipOneEqSuccAbove.lean#L49-L54

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

theorem P2M_PI_QnCovHatW_det_sub_eq__8094bc80bf43 {m : ℕ} (Q : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) (j j' : Fin (m + 1)) :
    ∑ σ : Equiv.Perm (Fin m), ((Equiv.Perm.sign σ : ℤ) : ℂ) *
        ∏ k, Q (j.succAbove k) ((j'.succAbove ∘ σ) k) =
      (Q.submatrix j.succAbove j'.succAbove).det := by sorry

alias «PI».«QnCovHatW».«det_sub_eq'» := P2M_PI_QnCovHatW_det_sub_eq__8094bc80bf43
