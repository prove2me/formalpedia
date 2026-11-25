-- Prove2me | Theorems.Thm_QnYLeibnizW_hasDerivAt_f
-- name    : QnYLeibnizW.hasDerivAt_f
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:31:02.240812+00:00
-- url     : https://prove2.me/theorems/abf85797-632f-4929-9ee9-34295112d6e4
-- title:
--   Qn YLeibniz W: has Deriv At f
-- statement:
--   The Qn YLeibniz W construction uses the has Deriv At f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ConjugateTransposeLeibniz/YOperatorLeibnizRule.lean#L224-L240
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ConjugateTransposeLeibniz/YOperatorLeibnizRule.lean#L224-L240

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

theorem QnYLeibnizW.hasDerivAt_f {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f F : Mx k r → E) (U : Set (Mx k r)) (g X : Mx k r) (hU : IsOpen U) (hgU : g ∈ U)
    (hg : g ∈ Glev k r i) (hF : ContDiffOn ℝ ∞ F U) (hfF : ∀ h ∈ U, h ∈ Glev k r i → f h = F h)
    (hX : inLieLev k r i X) :
    HasDerivAt (fun t : ℝ => f (g * NormedSpace.exp ((t : ℂ) • X))) (fderiv ℝ F g (g * X)) 0 := by sorry
