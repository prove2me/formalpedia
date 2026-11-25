-- Prove2me | Theorems.Thm_PI_SqfPrimeFactor_W_bad_disj
-- name    : PI.SqfPrimeFactor.W.bad_disj
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T08:27:01.522857+00:00
-- url     : https://prove2.me/theorems/bf6658e9-dbc6-4f1b-8d87-47f599ac7b0f
-- title:
--   W: bad disj
-- statement:
--   The W construction uses the bad disj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarefreePrimeFactor/SquarefreeCountEstimate.lean#L51-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarefreePrimeFactor/SquarefreeCountEstimate.lean#L51-L61

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

theorem PI.SqfPrimeFactor.W.bad_disj {r p p' : ℕ} (hp : r < 2 * p) (hp' : r < 2 * p') (hne : p ≠ p') :
    Disjoint (bad g r p) (bad g r p') := by sorry
