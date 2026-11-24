-- Prove2me | Theorems.Thm_QnYLeibnizW_hpart2_skew
-- name    : QnYLeibnizW.hpart2_skew
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T15:06:18.995523+00:00
-- url     : https://prove2.me/theorems/391b242c-4936-4415-abad-7fc2124105d6
-- title:
--   Qn YLeibniz W: hpart2 skew
-- statement:
--   The Qn YLeibniz W construction uses the hpart2 skew property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ConjugateTransposeLeibniz/YOperatorLeibnizRule.lean#L100-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ConjugateTransposeLeibniz/YOperatorLeibnizRule.lean#L100-L113

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

theorem QnYLeibnizW.hpart2_skew (H Z : Matrix (Fin n) (Fin n) ℂ) (hHh : Hᴴ = H) (hHH : H * H = 1) :
    (hpart2 H Z)ᴴ * H + H * hpart2 H Z = 0 := by sorry
