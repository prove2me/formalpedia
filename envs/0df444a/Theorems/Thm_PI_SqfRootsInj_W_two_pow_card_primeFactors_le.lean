-- Prove2me | Theorems.Thm_PI_SqfRootsInj_W_two_pow_card_primeFactors_le
-- name    : PI.SqfRootsInj.W.two_pow_card_primeFactors_le
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T08:28:08.072379+00:00
-- url     : https://prove2.me/theorems/f98ec9b7-690a-5a80-ab22-faee38668c7f
-- title:
--   W: two pow card prime Factors le
-- statement:
--   The W construction uses the two pow card prime Factors le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarefreeRootsInjective/TwoPowCardPrimeFactorsLe.lean#L23-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarefreeRootsInjective/TwoPowCardPrimeFactorsLe.lean#L23-L26

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeRootsInjective_ClaimOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeRootsInjective_TwoPowCardPrimeFactorsLe
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
open Classical
open PI PI.SqfRootsInj PI.SqfRootsInj.W
open PI.SqfLab

theorem PI.SqfRootsInj.W.two_pow_card_primeFactors_le {n : ℕ} (hn : n ≠ 0) : 2 ^ n.primeFactors.card ≤ n := by sorry
