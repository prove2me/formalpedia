-- Prove2me | Theorems.Thm_PI_SqfRootsInj_W_card_roots_X_pow_sub_X_le
-- name    : PI.SqfRootsInj.W.card_roots_X_pow_sub_X_le
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T08:27:29.96606+00:00
-- url     : https://prove2.me/theorems/cd25600e-1d24-49ff-ba70-328653378ede
-- title:
--   W: card roots X pow sub X le
-- statement:
--   The W construction uses the card roots X pow sub X le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarefreeRootsInjective/TwoPowCardPrimeFactorsLe.lean#L32-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarefreeRootsInjective/TwoPowCardPrimeFactorsLe.lean#L32-L35

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

theorem PI.SqfRootsInj.W.card_roots_X_pow_sub_X_le {K : Type*} [Field K] (M : ℕ) (hM : 2 ≤ M) :
    ((X ^ M - X : K[X]).roots.toFinset).card ≤ M := by sorry
