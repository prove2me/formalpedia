-- Prove2me | Theorems.Thm_PI_SqfPrimeFactor_W_mul_injOn
-- name    : PI.SqfPrimeFactor.W.mul_injOn
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T08:26:13.322722+00:00
-- url     : https://prove2.me/theorems/caf8bf33-e5a9-5dfb-acf7-5891bf5b3eb0
-- title:
--   W: mul inj On
-- statement:
--   The W construction uses the mul inj On property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarefreePrimeFactor/SquarefreeCountEstimate.lean#L24-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarefreePrimeFactor/SquarefreeCountEstimate.lean#L24-L36

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreePrimeFactor_MonicDegFnNatDegree
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreePrimeFactor_SquarefreeCountEstimate
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
noncomputable section
open PI PI.SqfPrimeFactor PI.SqfPrimeFactor.W
open PI.SqfLab
variable {g : ℕ} [Fact g.Prime]

theorem PI.SqfPrimeFactor.W.mul_injOn (r p : ℕ) (hp : r < 2 * p) :
    Set.InjOn (fun x : (ZMod g)[X] × (ZMod g)[X] => x.1 * x.2)
      ↑(irrDeg g p ×ˢ monicDeg g (r - p)) := by sorry
