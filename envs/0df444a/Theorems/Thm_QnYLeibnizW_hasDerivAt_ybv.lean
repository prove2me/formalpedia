-- Prove2me | Theorems.Thm_QnYLeibnizW_hasDerivAt_ybv
-- name    : QnYLeibnizW.hasDerivAt_ybv
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T05:51:37.13268+00:00
-- url     : https://prove2.me/theorems/e39d419a-3467-4d85-9f4c-d8eec85de212
-- title:
--   Qn YLeibniz W: has Deriv At ybv
-- statement:
--   The Qn YLeibniz W construction uses the has Deriv At ybv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ConjugateTransposeLeibniz/YOperatorLeibnizRule.lean#L258-L263
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ConjugateTransposeLeibniz/YOperatorLeibnizRule.lean#L258-L263

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

theorem QnYLeibnizW.hasDerivAt_ybv (z : Fin (2 * r + k + 1) → ℂ) (c : Fin (mdim k r i)) (g X : Mx k r) :
    HasDerivAt (fun t : ℝ => ybv k r z i (g * NormedSpace.exp ((t : ℂ) • X)) c)
      (herm (Hpk k r) ((g * X) *ᵥ bvec (posL k r i c)) (fvec k r z i)) 0 := by sorry
