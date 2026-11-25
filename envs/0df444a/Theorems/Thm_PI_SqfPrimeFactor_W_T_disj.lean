-- Prove2me | Theorems.Thm_PI_SqfPrimeFactor_W_T_disj
-- name    : PI.SqfPrimeFactor.W.T_disj
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T08:26:39.259643+00:00
-- url     : https://prove2.me/theorems/b4f37871-9945-4923-b80f-d0a30697a407
-- title:
--   W: T disj
-- statement:
--   The W construction uses the T disj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarefreePrimeFactor/SquarefreeCountEstimate.lean#L63-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarefreePrimeFactor/SquarefreeCountEstimate.lean#L63-L72

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

theorem PI.SqfPrimeFactor.W.T_disj (r p : ℕ) (hp : p ∈ bigPrimes r) (T : Finset (ZMod g)[X])
    (hT : ∀ f ∈ T, Ev g r f) : Disjoint T (bad g r p) := by sorry
