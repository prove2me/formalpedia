-- Prove2me | Theorems.Thm_QnYLeibnizW_hermL_apply
-- name    : QnYLeibnizW.hermL_apply
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T14:04:46.412623+00:00
-- url     : https://prove2.me/theorems/4e15bdc5-8a49-47b5-accc-216e51cda0bf
-- title:
--   Qn YLeibniz W: herm L apply
-- statement:
--   The Qn YLeibniz W construction uses the herm L apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ConjugateTransposeLeibniz/YOperatorLeibnizRule.lean#L33-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ConjugateTransposeLeibniz/YOperatorLeibnizRule.lean#L33-L34

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ConjugateTransposeLeibniz_ExpMulVecFix
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ConjugateTransposeLeibniz_YOperatorLeibnizRule
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
open scoped ContDiff
noncomputable section
open QnYLeibnizW
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}

theorem QnYLeibnizW.hermL_apply (H : Matrix (Fin n) (Fin n) ℂ) (w x : Fin n → ℂ) (M : Matrix (Fin n) (Fin n) ℂ) :
    hermL H w x M = herm H (M *ᵥ w) x := by sorry
