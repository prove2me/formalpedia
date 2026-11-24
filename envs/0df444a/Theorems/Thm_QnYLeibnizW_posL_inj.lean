-- Prove2me | Theorems.Thm_QnYLeibnizW_posL_inj
-- name    : QnYLeibnizW.posL_inj
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T15:06:42.575888+00:00
-- url     : https://prove2.me/theorems/154aea29-c895-4dda-bb64-f9d8d06618a0
-- title:
--   Qn YLeibniz W: pos L inj
-- statement:
--   The Qn YLeibniz W construction uses the pos L inj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ConjugateTransposeLeibniz/YOperatorLeibnizRule.lean#L123-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ConjugateTransposeLeibniz/YOperatorLeibnizRule.lean#L123-L131

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
variable {k r : ℕ} {i : Fin (r + 1)}

theorem QnYLeibnizW.posL_inj (a b : Fin (mdim k r i)) : posL k r i a = posL k r i b ↔ a = b := by sorry
