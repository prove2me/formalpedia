-- Prove2me | Theorems.Thm_PI_SqfRootsInj_W_cardA
-- name    : PI.SqfRootsInj.W.cardA
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T08:27:33.740064+00:00
-- url     : https://prove2.me/theorems/48f50612-d0d7-4f7c-9c62-b57aeb782f36
-- title:
--   W: card A
-- statement:
--   The W construction uses the card A property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarefreeRootsInjective/CardLeSumOfCover.lean#L83-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarefreeRootsInjective/CardLeSumOfCover.lean#L83-L112

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeRootsInjective_DivCount
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeRootsInjective_TwoPowCardPrimeFactorsLe
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeRootsInjective_CardLeSumOfCover
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

theorem PI.SqfRootsInj.W.cardA (g r : ℕ) [hg : Fact g.Prime] (T : Finset (ZMod g)[X])
    (hmon : ∀ f ∈ T, f.Monic ∧ f.natDegree = r) : (T.filter (PA g r)).card ≤ SA g r := by sorry
