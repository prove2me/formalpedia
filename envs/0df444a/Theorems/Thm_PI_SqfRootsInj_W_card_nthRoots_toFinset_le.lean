-- Prove2me | Theorems.Thm_PI_SqfRootsInj_W_card_nthRoots_toFinset_le
-- name    : PI.SqfRootsInj.W.card_nthRoots_toFinset_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:41:36.530456+00:00
-- url     : https://prove2.me/theorems/e4bc16c3-29ff-4b43-8fc8-f7457a448cf5
-- title:
--   W: card nth Roots to Finset le
-- statement:
--   The W construction uses the card nth Roots to Finset le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarefreeRootsInjective/TwoPowCardPrimeFactorsLe.lean#L28-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarefreeRootsInjective/TwoPowCardPrimeFactorsLe.lean#L28-L30

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

theorem PI.SqfRootsInj.W.card_nthRoots_toFinset_le {K : Type*} [Field K] (N : ℕ) (a : K) :
    (nthRoots N a).toFinset.card ≤ N := by sorry
