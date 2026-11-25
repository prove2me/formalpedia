-- Prove2me | Theorems.Thm_PI_SqfRootsInj_W_card_le_SA_SB
-- name    : PI.SqfRootsInj.W.card_le_SA_SB
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T08:27:23.20846+00:00
-- url     : https://prove2.me/theorems/feb1f3cb-9b24-412e-9007-c445942cb9f4
-- title:
--   W: card le SA SB
-- statement:
--   The W construction uses the card le SA SB property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarefreeRootsInjective/CardLeSumOfCover.lean#L160-L173
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarefreeRootsInjective/CardLeSumOfCover.lean#L160-L173

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

theorem PI.SqfRootsInj.W.card_le_SA_SB (g r : ℕ) [hg : Fact g.Prime] (T : Finset (ZMod g)[X])
    (hT : ∀ f ∈ T, IsLab g r f ∧ ∃ ℓ : ℕ, ℓ.Prime ∧ ℓ ∉ BB r g ∧
      (CaseA g r ℓ f ∨ CaseB g r ℓ f)) :
    T.card ≤ SA g r + SB g r := by sorry
