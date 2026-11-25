-- Prove2me | Theorems.Thm_QnYLeibnizW_hpart_kill
-- name    : QnYLeibnizW.hpart_kill
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T15:52:21.531934+00:00
-- url     : https://prove2.me/theorems/aee81a8e-c61f-4f9e-90b3-586b689e12f0
-- title:
--   Qn YLeibniz W: hpart kill
-- statement:
--   The Qn YLeibniz W construction uses the hpart kill property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ConjugateTransposeLeibniz/YOperatorLeibnizRule.lean#L153-L188
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ConjugateTransposeLeibniz/YOperatorLeibnizRule.lean#L153-L188

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

theorem QnYLeibnizW.hpart_kill (a b : Fin (mdim k r i)) (q : Fin (2 * r + k + 1))
    (hq : q.val < i.val ∨ 2 * r + k < q.val + i.val) :
    hpart1 (Hpk k r) (Matrix.single (posL k r i a) (posL k r i b) 1) *ᵥ bvec q = 0 ∧
      hpart2 (Hpk k r) (Matrix.single (posL k r i a) (posL k r i b) 1) *ᵥ bvec q = 0 := by sorry
